use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering as AtomicOrdering};

#[cfg(unix)]
mod sys_mmap {
    use std::fs::File;
    use std::os::unix::io::AsRawFd;
    use std::ptr;

    pub struct MmapFile {
        ptr: *const u8,
        len: usize,
    }

    impl MmapFile {
        pub fn open(file: &File, len: usize) -> Result<Self, String> {
            if len == 0 {
                return Ok(Self {
                    ptr: ptr::null(),
                    len: 0,
                });
            }
            unsafe {
                let addr = libc_mmap(
                    ptr::null_mut(),
                    len,
                    PROT_READ,
                    MAP_PRIVATE,
                    file.as_raw_fd(),
                    0,
                );
                if addr == MAP_FAILED {
                    return Err("mmap failed".to_string());
                }
                Ok(Self {
                    ptr: addr as *const u8,
                    len,
                })
            }
        }

        #[inline]
        pub fn as_slice(&self) -> &[u8] {
            if self.len == 0 || self.ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
            }
        }
    }

    impl Drop for MmapFile {
        fn drop(&mut self) {
            if !self.ptr.is_null() && self.len > 0 {
                unsafe {
                    libc_munmap(self.ptr as *mut _, self.len);
                }
            }
        }
    }

    unsafe impl Send for MmapFile {}
    unsafe impl Sync for MmapFile {}

    const PROT_READ: i32 = 1;
    const MAP_PRIVATE: i32 = 2;
    const MAP_FAILED: *mut libc_c_void = !0 as *mut libc_c_void;

    type libc_c_void = std::ffi::c_void;
    type libc_size_t = usize;
    type libc_off_t = i64;
    type libc_c_int = i32;

    extern "C" {
        #[link_name = "mmap"]
        fn libc_mmap(
            addr: *mut libc_c_void,
            len: libc_size_t,
            prot: libc_c_int,
            flags: libc_c_int,
            fd: libc_c_int,
            offset: libc_off_t,
        ) -> *mut libc_c_void;

        #[link_name = "munmap"]
        fn libc_munmap(addr: *mut libc_c_void, len: libc_size_t) -> libc_c_int;
    }
}

pub enum InputBuffer {
    #[cfg(unix)]
    Mmap(sys_mmap::MmapFile),
    Vec(Vec<u8>),
}

impl InputBuffer {
    pub fn open(path: &Path) -> Result<Self, String> {
        let file = fs::File::open(path).map_err(|e| e.to_string())?;
        let metadata = file.metadata().map_err(|e| e.to_string())?;
        let len = metadata.len() as usize;

        #[cfg(unix)]
        {
            if let Ok(mmap) = sys_mmap::MmapFile::open(&file, len) {
                return Ok(InputBuffer::Mmap(mmap));
            }
        }

        let bytes = fs::read(path).map_err(|e| e.to_string())?;
        Ok(InputBuffer::Vec(bytes))
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        match self {
            #[cfg(unix)]
            InputBuffer::Mmap(m) => m.as_slice(),
            InputBuffer::Vec(v) => v.as_slice(),
        }
    }
}

pub fn partition_byte_ranges(data: &[u8], num_chunks: usize) -> Vec<&[u8]> {
    if data.is_empty() || num_chunks <= 1 {
        return vec![data];
    }
    let total_len = data.len();
    let mut boundaries = Vec::with_capacity(num_chunks + 1);
    boundaries.push(0);

    for i in 1..num_chunks {
        let tentative = (i * total_len) / num_chunks;
        let mut b = tentative;
        while b < total_len && data[b] != b'\n' {
            b += 1;
        }
        if b < total_len {
            b += 1; // Advance past newline so next chunk starts on a fresh line
        }
        let prev = *boundaries.last().unwrap();
        if b < prev {
            b = prev;
        }
        boundaries.push(b);
    }
    boundaries.push(total_len);

    let mut chunks = Vec::with_capacity(num_chunks);
    for w in boundaries.windows(2) {
        chunks.push(&data[w[0]..w[1]]);
    }
    chunks
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct State {
    pub cost: u64,
    pub node: u32,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
pub struct CsrGraph {
    pub num_nodes: u32,
    pub raw_edge_count: usize,
    pub retained_edge_count: usize,
    pub offsets: Vec<u32>,
    pub head: Vec<u32>,
    pub weight: Vec<u32>,
    pub rev_offsets: Vec<u32>,
    pub rev_head: Vec<u32>,
    pub rev_weight: Vec<u32>,
    pub wcc: Vec<u32>,
}

impl CsrGraph {
    #[inline]
    pub fn out_deg(&self, u: u32) -> u32 {
        let u_idx = u as usize;
        if u_idx + 1 < self.offsets.len() {
            self.offsets[u_idx + 1] - self.offsets[u_idx]
        } else {
            0
        }
    }

    #[inline]
    pub fn in_deg(&self, v: u32) -> u32 {
        let v_idx = v as usize;
        if v_idx + 1 < self.rev_offsets.len() {
            self.rev_offsets[v_idx + 1] - self.rev_offsets[v_idx]
        } else {
            0
        }
    }

    #[inline]
    pub fn neighbors(&self, u: u32) -> impl Iterator<Item = (u32, u32)> + '_ {
        let start = self.offsets[u as usize] as usize;
        let end = self.offsets[(u + 1) as usize] as usize;
        (start..end).map(move |i| (self.head[i], self.weight[i]))
    }

    #[inline]
    pub fn rev_neighbors(&self, v: u32) -> impl Iterator<Item = (u32, u32)> + '_ {
        let start = self.rev_offsets[v as usize] as usize;
        let end = self.rev_offsets[(v + 1) as usize] as usize;
        (start..end).map(move |i| (self.rev_head[i], self.rev_weight[i]))
    }
}

pub struct FastParser<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> FastParser<'a> {
    #[inline]
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    #[inline]
    fn skip_whitespace(&mut self) {
        while self.pos < self.data.len()
            && (self.data[self.pos] == b' '
                || self.data[self.pos] == b'\t'
                || self.data[self.pos] == b'\n'
                || self.data[self.pos] == b'\r')
        {
            self.pos += 1;
        }
    }

    #[inline]
    pub fn parse_u32(&mut self) -> Result<u32, String> {
        self.skip_whitespace();
        if self.pos >= self.data.len() {
            return Err("unexpected EOF".to_string());
        }
        let start = self.pos;
        let mut val = 0u32;
        while self.pos < self.data.len()
            && self.data[self.pos] >= b'0'
            && self.data[self.pos] <= b'9'
        {
            let digit = (self.data[self.pos] - b'0') as u32;
            val = val
                .checked_mul(10)
                .and_then(|v| v.checked_add(digit))
                .ok_or_else(|| "u32 integer overflow".to_string())?;
            self.pos += 1;
        }
        if self.pos == start {
            return Err("expected digit".to_string());
        }
        Ok(val)
    }

    #[inline]
    pub fn parse_u64(&mut self) -> Result<u64, String> {
        self.skip_whitespace();
        if self.pos >= self.data.len() {
            return Err("unexpected EOF".to_string());
        }
        let start = self.pos;
        let mut val = 0u64;
        while self.pos < self.data.len()
            && self.data[self.pos] >= b'0'
            && self.data[self.pos] <= b'9'
        {
            let digit = (self.data[self.pos] - b'0') as u64;
            val = val
                .checked_mul(10)
                .and_then(|v| v.checked_add(digit))
                .ok_or_else(|| "u64 integer overflow".to_string())?;
            self.pos += 1;
        }
        if self.pos == start {
            return Err("expected digit".to_string());
        }
        Ok(val)
    }

    #[inline]
    pub fn has_more(&mut self) -> bool {
        self.skip_whitespace();
        self.pos < self.data.len()
    }
}

pub struct Dsu {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl Dsu {
    pub fn new(n: u32) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n as usize],
        }
    }

    pub fn find(&mut self, mut x: u32) -> u32 {
        let mut root = x;
        while root != self.parent[root as usize] {
            root = self.parent[root as usize];
        }
        while x != root {
            let next = self.parent[x as usize];
            self.parent[x as usize] = root;
            x = next;
        }
        root
    }

    pub fn union(&mut self, a: u32, b: u32) {
        let root_a = self.find(a);
        let root_b = self.find(b);
        if root_a != root_b {
            let rank_a = self.rank[root_a as usize];
            let rank_b = self.rank[root_b as usize];
            if rank_a < rank_b {
                self.parent[root_a as usize] = root_b;
            } else if rank_a > rank_b {
                self.parent[root_b as usize] = root_a;
            } else {
                self.parent[root_b as usize] = root_a;
                self.rank[root_a as usize] += 1;
            }
        }
    }
}

pub struct BitSet {
    words: Vec<u64>,
}

impl BitSet {
    pub fn new(num_bits: usize) -> Self {
        let num_words = (num_bits + 63) / 64;
        Self {
            words: vec![0u64; num_words],
        }
    }

    #[inline]
    pub fn get(&self, idx: usize) -> bool {
        let word_idx = idx / 64;
        let bit_idx = idx % 64;
        (self.words[word_idx] & (1u64 << bit_idx)) != 0
    }

    #[inline]
    pub fn set(&mut self, idx: usize, val: bool) {
        let word_idx = idx / 64;
        let bit_idx = idx % 64;
        if val {
            self.words[word_idx] |= 1u64 << bit_idx;
        } else {
            self.words[word_idx] &= !(1u64 << bit_idx);
        }
    }
}

struct SyncSlice<T>(*mut T, usize);
unsafe impl<T: Send> Send for SyncSlice<T> {}
unsafe impl<T: Sync> Sync for SyncSlice<T> {}

impl<T> SyncSlice<T> {
    #[inline]
    unsafe fn write(&self, index: usize, val: T) {
        debug_assert!(index < self.1);
        *self.0.add(index) = val;
    }
}

/// Track D V3: Parallel Graph Parser with 2-Pass Direct CSR and deterministic deduplication
pub fn parse_graph(data: &[u8]) -> Result<CsrGraph, String> {
    let mut header_parser = FastParser::new(data);
    let n = header_parser.parse_u32()?;
    let m = header_parser.parse_u32()? as usize;
    header_parser.skip_whitespace();
    let body_start = header_parser.pos;
    let body = &data[body_start..];

    let num_parse_threads = env::var("PARSE_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(4)
                .min(4)
        });

    let chunks = partition_byte_ranges(body, num_parse_threads);

    // PASS 1: Parallel count of raw out-degrees per node (skipping self-loops)
    let raw_out_degrees: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();

    let pass1_res: Result<Vec<usize>, String> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in &chunks {
            let deg_ref = &raw_out_degrees;
            handles.push(s.spawn(move || -> Result<usize, String> {
                let mut parser = FastParser::new(chunk);
                let mut edge_count = 0usize;
                while parser.has_more() {
                    let u = parser.parse_u32()?;
                    let v = parser.parse_u32()?;
                    let w = parser.parse_u64()?;

                    if u >= n || v >= n {
                        return Err(format!("node id out of bounds: u={}, v={}, n={}", u, v, n));
                    }
                    if w > u32::MAX as u64 {
                        return Err(format!("weight exceeds u32::MAX: {}", w));
                    }

                    if u != v {
                        deg_ref[u as usize].fetch_add(1, AtomicOrdering::Relaxed);
                    }
                    edge_count += 1;
                }
                Ok(edge_count)
            }));
        }

        let mut counts = Vec::with_capacity(handles.len());
        for h in handles {
            counts.push(h.join().unwrap()?);
        }
        Ok(counts)
    });

    let chunk_counts = pass1_res?;
    let total_parsed_m: usize = chunk_counts.iter().sum();
    if total_parsed_m != m {
        return Err(format!("expected {} edges in header, found {}", m, total_parsed_m));
    }

    // Prefix sum raw out-degrees into forward offsets
    let mut raw_offsets = vec![0u32; (n + 1) as usize];
    for u in 0..n {
        let deg = raw_out_degrees[u as usize].load(AtomicOrdering::Relaxed);
        raw_offsets[(u + 1) as usize] = raw_offsets[u as usize] + deg;
    }
    let total_valid_edges = raw_offsets[n as usize] as usize;

    drop(raw_out_degrees);

    // PASS 2: Parallel scatter of edges directly into head and weight
    let mut head = vec![0u32; total_valid_edges];
    let mut weight = vec![0u32; total_valid_edges];

    let cursor: Vec<AtomicU32> = (0..n)
        .map(|u| AtomicU32::new(raw_offsets[u as usize]))
        .collect();

    let head_ptr = SyncSlice(head.as_mut_ptr(), total_valid_edges);
    let weight_ptr = SyncSlice(weight.as_mut_ptr(), total_valid_edges);

    let pass2_res: Result<(), String> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in &chunks {
            let cursor_ref = &cursor;
            let hp = &head_ptr;
            let wp = &weight_ptr;
            handles.push(s.spawn(move || -> Result<(), String> {
                let mut parser = FastParser::new(chunk);
                while parser.has_more() {
                    let u = parser.parse_u32()?;
                    let v = parser.parse_u32()?;
                    let w = parser.parse_u64()? as u32;

                    if u != v {
                        let slot = cursor_ref[u as usize].fetch_add(1, AtomicOrdering::Relaxed) as usize;
                        unsafe {
                            hp.write(slot, v);
                            wp.write(slot, w);
                        }
                    }
                }
                Ok(())
            }));
        }

        for h in handles {
            h.join().unwrap()?;
        }
        Ok(())
    });
    pass2_res?;

    drop(cursor);

    // In-place deduplication: sort out-edges for each node u and retain min weight for parallel copies
    let mut final_offsets = vec![0u32; (n + 1) as usize];
    let mut write_idx = 0usize;
    let mut u_adj: Vec<(u32, u32)> = Vec::with_capacity(32);

    for u in 0..n {
        final_offsets[u as usize] = write_idx as u32;
        let start = raw_offsets[u as usize] as usize;
        let end = raw_offsets[(u + 1) as usize] as usize;

        if start < end {
            u_adj.clear();
            for i in start..end {
                u_adj.push((head[i], weight[i]));
            }
            u_adj.sort_unstable_by_key(|&(v, w)| (v, w));

            let mut prev_v: Option<u32> = None;
            for &(v, w) in &u_adj {
                if prev_v == Some(v) {
                    continue; // Skip parallel copy with heavier/equal weight
                }
                prev_v = Some(v);
                head[write_idx] = v;
                weight[write_idx] = w;
                write_idx += 1;
            }
        }
    }
    final_offsets[n as usize] = write_idx as u32;
    head.truncate(write_idx);
    weight.truncate(write_idx);
    let retained_edge_count = write_idx;

    drop(raw_offsets);

    // Build Backward CSR from the deduplicated forward edges
    let mut rev_offsets = vec![0u32; (n + 1) as usize];
    for &v in &head {
        rev_offsets[(v + 1) as usize] += 1;
    }
    for v in 0..n {
        rev_offsets[(v + 1) as usize] += rev_offsets[v as usize];
    }

    let mut rev_head = vec![0u32; retained_edge_count];
    let mut rev_weight = vec![0u32; retained_edge_count];
    let mut rev_cursor = rev_offsets.clone();

    for u in 0..n {
        let start = final_offsets[u as usize] as usize;
        let end = final_offsets[(u + 1) as usize] as usize;
        for i in start..end {
            let v = head[i];
            let w = weight[i];
            let slot = rev_cursor[v as usize] as usize;
            rev_head[slot] = u;
            rev_weight[slot] = w;
            rev_cursor[v as usize] += 1;
        }
    }

    // Build WCC on deduplicated forward edges
    let mut dsu = Dsu::new(n);
    for u in 0..n {
        let start = final_offsets[u as usize] as usize;
        let end = final_offsets[(u + 1) as usize] as usize;
        for i in start..end {
            dsu.union(u, head[i]);
        }
    }

    let mut wcc = vec![0u32; n as usize];
    for u in 0..n {
        wcc[u as usize] = dsu.find(u);
    }

    Ok(CsrGraph {
        num_nodes: n,
        raw_edge_count: m,
        retained_edge_count,
        offsets: final_offsets,
        head,
        weight,
        rev_offsets,
        rev_head,
        rev_weight,
        wcc,
    })
}

pub struct DijkstraContext {
    pub dist_f: Box<[u64]>,
    pub dist_b: Box<[u64]>,
    pub settled_f: BitSet,
    pub settled_b: BitSet,
    pub visited_f: Vec<u32>,
    pub visited_b: Vec<u32>,
    pub settled_nodes_f: Vec<u32>,
    pub settled_nodes_b: Vec<u32>,
    pub heap_f: BinaryHeap<State>,
    pub heap_b: BinaryHeap<State>,
    pub total_settled_nodes: usize,
}

impl DijkstraContext {
    pub fn new(num_nodes: u32) -> Self {
        let n = num_nodes as usize;
        Self {
            dist_f: vec![u64::MAX; n].into_boxed_slice(),
            dist_b: vec![u64::MAX; n].into_boxed_slice(),
            settled_f: BitSet::new(n),
            settled_b: BitSet::new(n),
            visited_f: Vec::with_capacity(1024),
            visited_b: Vec::with_capacity(1024),
            settled_nodes_f: Vec::with_capacity(512),
            settled_nodes_b: Vec::with_capacity(512),
            heap_f: BinaryHeap::with_capacity(1024),
            heap_b: BinaryHeap::with_capacity(1024),
            total_settled_nodes: 0,
        }
    }

    #[inline]
    pub fn reset(&mut self) {
        for &node in &self.visited_f {
            self.dist_f[node as usize] = u64::MAX;
        }
        self.visited_f.clear();

        for &node in &self.visited_b {
            self.dist_b[node as usize] = u64::MAX;
        }
        self.visited_b.clear();

        for &node in &self.settled_nodes_f {
            self.settled_f.set(node as usize, false);
        }
        self.settled_nodes_f.clear();

        for &node in &self.settled_nodes_b {
            self.settled_b.set(node as usize, false);
        }
        self.settled_nodes_b.clear();
    }

    pub fn sequential_shortest_path(&mut self, graph: &CsrGraph, s: u32, t: u32) -> i64 {
        if s == t {
            return 0;
        }
        if graph.wcc[s as usize] != graph.wcc[t as usize] {
            return -1;
        }
        if graph.out_deg(s) == 0 || graph.in_deg(t) == 0 {
            return -1;
        }

        self.reset();
        self.heap_f.clear();

        let s_idx = s as usize;
        self.visited_f.push(s);
        self.dist_f[s_idx] = 0;
        self.heap_f.push(State { cost: 0, node: s });

        let mut result = -1i64;
        while let Some(State { cost, node }) = self.heap_f.pop() {
            let node_idx = node as usize;
            if cost > self.dist_f[node_idx] {
                continue;
            }
            self.total_settled_nodes += 1;

            if node == t {
                result = cost as i64;
                break;
            }

            for (v, w) in graph.neighbors(node) {
                let v_idx = v as usize;
                let next_cost = cost.saturating_add(w as u64);

                if self.dist_f[v_idx] == u64::MAX {
                    self.visited_f.push(v);
                    self.dist_f[v_idx] = next_cost;
                    self.heap_f.push(State {
                        cost: next_cost,
                        node: v,
                    });
                } else if next_cost < self.dist_f[v_idx] {
                    self.dist_f[v_idx] = next_cost;
                    self.heap_f.push(State {
                        cost: next_cost,
                        node: v,
                    });
                }
            }
        }

        self.reset();
        result
    }

    pub fn bidirectional_shortest_path(&mut self, graph: &CsrGraph, s: u32, t: u32) -> i64 {
        if s == t {
            return 0;
        }
        if graph.wcc[s as usize] != graph.wcc[t as usize] {
            return -1;
        }
        if graph.out_deg(s) == 0 || graph.in_deg(t) == 0 {
            return -1;
        }

        self.reset();
        self.heap_f.clear();
        self.heap_b.clear();

        let s_idx = s as usize;
        self.visited_f.push(s);
        self.dist_f[s_idx] = 0;
        self.heap_f.push(State { cost: 0, node: s });

        let t_idx = t as usize;
        self.visited_b.push(t);
        self.dist_b[t_idx] = 0;
        self.heap_b.push(State { cost: 0, node: t });

        let mut mu: u64 = u64::MAX;

        loop {
            let top_f = self.heap_f.peek().map(|s| s.cost);
            let top_b = self.heap_b.peek().map(|s| s.cost);

            if top_f.is_none() && top_b.is_none() {
                break;
            }

            if let (Some(df), Some(db)) = (top_f, top_b) {
                if df.saturating_add(db) >= mu {
                    break;
                }
            }

            let expand_forward = match (top_f, top_b) {
                (Some(df), Some(db)) => df <= db,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };

            if expand_forward {
                let State { cost, node } = self.heap_f.pop().unwrap();
                let node_idx = node as usize;
                if cost > self.dist_f[node_idx] {
                    continue;
                }
                if self.settled_f.get(node_idx) {
                    continue;
                }
                self.settled_f.set(node_idx, true);
                self.settled_nodes_f.push(node);
                self.total_settled_nodes += 1;

                if self.dist_b[node_idx] != u64::MAX {
                    mu = mu.min(cost.saturating_add(self.dist_b[node_idx]));
                }

                for (v, w) in graph.neighbors(node) {
                    let v_idx = v as usize;
                    let next_cost = cost.saturating_add(w as u64);

                    if self.dist_f[v_idx] == u64::MAX {
                        self.visited_f.push(v);
                        self.dist_f[v_idx] = next_cost;
                        self.heap_f.push(State {
                            cost: next_cost,
                            node: v,
                        });

                        if self.dist_b[v_idx] != u64::MAX {
                            mu = mu.min(next_cost.saturating_add(self.dist_b[v_idx]));
                        }
                    } else if next_cost < self.dist_f[v_idx] {
                        self.dist_f[v_idx] = next_cost;
                        self.heap_f.push(State {
                            cost: next_cost,
                            node: v,
                        });

                        if self.dist_b[v_idx] != u64::MAX {
                            mu = mu.min(next_cost.saturating_add(self.dist_b[v_idx]));
                        }
                    }
                }
            } else {
                let State { cost, node } = self.heap_b.pop().unwrap();
                let node_idx = node as usize;
                if cost > self.dist_b[node_idx] {
                    continue;
                }
                if self.settled_b.get(node_idx) {
                    continue;
                }
                self.settled_b.set(node_idx, true);
                self.settled_nodes_b.push(node);
                self.total_settled_nodes += 1;

                if self.dist_f[node_idx] != u64::MAX {
                    mu = mu.min(self.dist_f[node_idx].saturating_add(cost));
                }

                for (u, w) in graph.rev_neighbors(node) {
                    let u_idx = u as usize;
                    let next_cost = cost.saturating_add(w as u64);

                    if self.dist_b[u_idx] == u64::MAX {
                        self.visited_b.push(u);
                        self.dist_b[u_idx] = next_cost;
                        self.heap_b.push(State {
                            cost: next_cost,
                            node: u,
                        });

                        if self.dist_f[u_idx] != u64::MAX {
                            mu = mu.min(self.dist_f[u_idx].saturating_add(next_cost));
                        }
                    } else if next_cost < self.dist_b[u_idx] {
                        self.dist_b[u_idx] = next_cost;
                        self.heap_b.push(State {
                            cost: next_cost,
                            node: u,
                        });

                        if self.dist_f[u_idx] != u64::MAX {
                            mu = mu.min(self.dist_f[u_idx].saturating_add(next_cost));
                        }
                    }
                }
            }
        }

        let ans = if mu == u64::MAX { -1 } else { mu as i64 };
        self.reset();
        ans
    }
}

pub fn parse_queries(data: &[u8]) -> Result<Vec<(u32, u32)>, String> {
    let mut parser = FastParser::new(data);
    let mut queries = Vec::new();
    while parser.has_more() {
        let s = parser.parse_u32()?;
        let t = parser.parse_u32()?;
        queries.push((s, t));
    }
    Ok(queries)
}

pub fn run_traverse(graph_data: &[u8], queries_data: &[u8]) -> Result<Vec<u8>, String> {
    let graph = parse_graph(graph_data)?;
    let queries = parse_queries(queries_data)?;

    let mut ctx = DijkstraContext::new(graph.num_nodes);
    let mut output = String::with_capacity(queries.len() * 12);

    for (s, t) in queries {
        let dist = ctx.bidirectional_shortest_path(&graph, s, t);
        writeln!(&mut output, "{}", dist).unwrap();
    }

    Ok(output.into_bytes())
}

pub fn parallel_bidirectional_traverse(
    graph: &CsrGraph,
    queries: &[(u32, u32)],
    num_threads: usize,
) -> (Vec<i64>, usize) {
    if queries.is_empty() {
        return (Vec::new(), 0);
    }
    let actual_threads = num_threads.max(1).min(queries.len());
    let next_query_idx = AtomicUsize::new(0);

    let thread_results: Vec<(Vec<(usize, i64)>, usize)> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(actual_threads);
        for _ in 0..actual_threads {
            let next_idx_ref = &next_query_idx;
            handles.push(s.spawn(move || {
                let mut ctx = DijkstraContext::new(graph.num_nodes);
                let mut local_results = Vec::with_capacity(queries.len() / actual_threads + 32);

                loop {
                    let idx = next_idx_ref.fetch_add(1, AtomicOrdering::Relaxed);
                    if idx >= queries.len() {
                        break;
                    }
                    let (s_node, t_node) = queries[idx];
                    let dist = ctx.bidirectional_shortest_path(graph, s_node, t_node);
                    local_results.push((idx, dist));
                }

                (local_results, ctx.total_settled_nodes)
            }));
        }

        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut answers = vec![0i64; queries.len()];
    let mut total_settled = 0;

    for (local_results, settled) in thread_results {
        total_settled += settled;
        for (idx, ans) in local_results {
            answers[idx] = ans;
        }
    }

    (answers, total_settled)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let graph_path = Path::new(data_dir).join("graph.txt");
    let queries_path = Path::new(data_dir).join("queries.txt");

    if !graph_path.exists() || !queries_path.exists() {
        eprintln!(
            "Input files missing: {} or {}",
            graph_path.display(),
            queries_path.display()
        );
        std::process::exit(1);
    }

    let graph_buf = InputBuffer::open(&graph_path).expect("failed to open graph.txt");
    let queries_buf = InputBuffer::open(&queries_path).expect("failed to open queries.txt");

    let t_graph_start = std::time::Instant::now();
    let graph = parse_graph(graph_buf.as_slice()).expect("graph parse failed");
    let t_graph_elapsed = t_graph_start.elapsed();

    eprintln!(
        "Graph parsed in {:?}: {} nodes, {} raw edges, {} retained edges (deduped)",
        t_graph_elapsed, graph.num_nodes, graph.raw_edge_count, graph.retained_edge_count
    );

    let t_queries_start = std::time::Instant::now();
    let queries = parse_queries(queries_buf.as_slice()).expect("queries parse failed");
    let t_queries_elapsed = t_queries_start.elapsed();
    eprintln!("Queries parsed in {:?}: {} queries", t_queries_elapsed, queries.len());

    let bench_mode = env::var("BENCH_MODE").unwrap_or_default();
    let num_threads = env::var("NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);

    let (answers, total_settled, mode_name, duration) = match bench_mode.as_str() {
        "seq" => {
            let mut seq_ctx = DijkstraContext::new(graph.num_nodes);
            let start = std::time::Instant::now();
            let mut ans = Vec::with_capacity(queries.len());
            for &(s, t) in &queries {
                ans.push(seq_ctx.sequential_shortest_path(&graph, s, t));
            }
            let dur = start.elapsed();
            (ans, seq_ctx.total_settled_nodes, "Sequential Dijkstra (1 thread)", dur)
        }
        "bidi_1" => {
            let mut bidi_ctx = DijkstraContext::new(graph.num_nodes);
            let start = std::time::Instant::now();
            let mut ans = Vec::with_capacity(queries.len());
            for &(s, t) in &queries {
                ans.push(bidi_ctx.bidirectional_shortest_path(&graph, s, t));
            }
            let dur = start.elapsed();
            (ans, bidi_ctx.total_settled_nodes, "Single-threaded Bidirectional Dijkstra (1 thread)", dur)
        }
        _ => {
            let start = std::time::Instant::now();
            let (ans, settled) = parallel_bidirectional_traverse(&graph, &queries, num_threads);
            let dur = start.elapsed();
            (ans, settled, "Multithreaded Bidirectional Dijkstra", dur)
        }
    };

    eprintln!(
        "Evaluation finished [{}]: {:?} across {} queries ({} total nodes settled, {} threads)",
        mode_name,
        duration,
        queries.len(),
        total_settled,
        if bench_mode == "seq" || bench_mode == "bidi_1" { 1 } else { num_threads }
    );

    let t_write_start = std::time::Instant::now();
    let mut output = String::with_capacity(answers.len() * 12);
    for dist in answers {
        writeln!(&mut output, "{}", dist).unwrap();
    }

    let output_bytes = output.into_bytes();

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create output directory");
    let out_file_path = out_dir_path.join("distances.txt");

    let mut file = fs::File::create(&out_file_path).expect("failed to create distances.txt");
    file.write_all(&output_bytes)
        .expect("failed to write distances.txt");
    file.flush().expect("failed to flush distances.txt");
    eprintln!("Output written in {:?}", t_write_start.elapsed());

    if let Ok(status) = fs::read_to_string("/proc/self/status") {
        for line in status.lines() {
            if line.starts_with("VmHWM:") || line.starts_with("RssAnon:") || line.starts_with("RssFile:") {
                eprintln!("{}", line.trim());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const WORKED_GRAPH: &[u8] = b"8 12\n\
0 1 4\n\
1 2 3\n\
0 2 9\n\
2 0 5\n\
2 1 6\n\
1 3 0\n\
3 4 0\n\
4 4 7\n\
4 5 4294967295\n\
2 1 2\n\
5 6 4294967295\n\
0 1 4\n";

    const WORKED_QUERIES: &[u8] = b"0 2\n\
2 1\n\
1 4\n\
4 4\n\
7 7\n\
0 6\n\
4 5\n\
6 0\n\
0 7\n\
1 0\n\
2 1\n";

    const WORKED_EXPECTED: &[u8] = b"7\n\
2\n\
0\n\
0\n\
0\n\
8589934594\n\
4294967295\n\
-1\n\
-1\n\
8\n\
2\n";

    #[test]
    fn test_worked_example_end_to_end() {
        let out = run_traverse(WORKED_GRAPH, WORKED_QUERIES).unwrap();
        assert_eq!(out, WORKED_EXPECTED);
    }

    #[test]
    fn test_self_queries_isolated_nodes() {
        let graph_bytes = b"5 0\n";
        let queries_bytes = b"0 0\n1 1\n4 4\n0 1\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"0\n0\n0\n-1\n");
    }

    #[test]
    fn test_zero_weight_paths() {
        let graph_bytes = b"4 3\n0 1 0\n1 2 0\n2 3 0\n";
        let queries_bytes = b"0 3\n1 3\n3 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"0\n0\n-1\n");
    }

    #[test]
    fn test_max_u32_edge_weights_and_overflow() {
        let max_w = u32::MAX;
        let graph_bytes = format!("4 3\n0 1 {}\n1 2 {}\n2 3 {}\n", max_w, max_w, max_w);
        let queries_bytes = b"0 1\n0 2\n0 3\n";
        let out = run_traverse(graph_bytes.as_bytes(), queries_bytes).unwrap();
        let expected = format!(
            "{}\n{}\n{}\n",
            max_w,
            max_w as u64 * 2,
            max_w as u64 * 3
        );
        assert_eq!(out, expected.as_bytes());
    }

    #[test]
    fn test_parallel_edges_and_duplicate_lines() {
        let graph_bytes = b"3 5\n0 1 100\n0 1 20\n0 1 20\n0 1 50\n1 2 5\n";
        let queries_bytes = b"0 1\n0 2\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"20\n25\n");
    }

    #[test]
    fn test_self_loops_ignored() {
        let graph_bytes = b"3 5\n0 0 1\n0 1 10\n1 1 0\n1 2 20\n2 2 100\n";
        let queries_bytes = b"0 0\n1 1\n2 2\n0 2\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"0\n0\n0\n30\n");
    }

    #[test]
    fn test_unreachable_degree_filters_and_disconnected() {
        let graph_bytes = b"6 3\n0 1 10\n1 2 10\n3 4 5\n";
        let queries_bytes = b"0 2\n2 0\n1 0\n0 4\n5 5\n5 0\n0 5\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"20\n-1\n-1\n-1\n0\n-1\n-1\n");
    }

    #[test]
    fn test_multi_hop_paths_exceeding_u32() {
        let w = 3_000_000_000u64;
        let graph_bytes = format!("3 2\n0 1 {}\n1 2 {}\n", w, w);
        let queries_bytes = b"0 2\n";
        let out = run_traverse(graph_bytes.as_bytes(), queries_bytes).unwrap();
        assert_eq!(out, format!("{}\n", w * 2).as_bytes());
    }

    #[test]
    fn test_duplicate_edges() {
        let graph_bytes = b"2 3\n0 1 42\n0 1 42\n0 1 42\n";
        let queries_bytes = b"0 1\n1 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"42\n-1\n");
    }

    #[test]
    fn test_disconnected_components() {
        let graph_bytes = b"4 4\n0 1 5\n1 0 5\n2 3 10\n3 2 10\n";
        let queries_bytes = b"0 1\n1 0\n2 3\n0 2\n1 3\n3 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"5\n5\n10\n-1\n-1\n-1\n");
    }

    #[test]
    fn test_asymmetric_directed_paths() {
        let graph_bytes = b"3 3\n0 1 2\n1 2 3\n2 0 10\n";
        let queries_bytes = b"0 2\n2 0\n2 1\n1 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"5\n10\n12\n13\n");
    }

    #[test]
    fn test_multiple_crossing_edges_and_meeting_vertices() {
        let graph_bytes = b"6 7\n0 1 1\n1 2 10\n2 5 1\n0 3 5\n3 4 1\n4 5 5\n1 4 2\n";
        let queries_bytes = b"0 5\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"8\n");
    }

    struct SimpleRng {
        state: u64,
    }
    impl SimpleRng {
        fn new(seed: u64) -> Self {
            Self { state: seed }
        }
        fn next_u32(&mut self) -> u32 {
            self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
            (self.state >> 32) as u32
        }
        fn gen_range(&mut self, low: u32, high: u32) -> u32 {
            low + (self.next_u32() % (high - low + 1))
        }
    }

    #[test]
    fn test_randomized_differential_dijkstra() {
        let mut rng = SimpleRng::new(0xDEADBEEFCAFE);

        for _ in 0..50 {
            let n = rng.gen_range(5, 30);
            let m = rng.gen_range(5, 80);

            let mut graph_str = format!("{} {}\n", n, m);
            for _ in 0..m {
                let u = rng.gen_range(0, n - 1);
                let v = rng.gen_range(0, n - 1);
                let w = if rng.gen_range(0, 10) == 0 {
                    0
                } else {
                    rng.gen_range(1, 1000)
                };
                graph_str.push_str(&format!("{} {} {}\n", u, v, w));
            }

            let graph = parse_graph(graph_str.as_bytes()).unwrap();
            let mut ctx = DijkstraContext::new(graph.num_nodes);

            for s in 0..n {
                for t in 0..n {
                    let seq_ans = ctx.sequential_shortest_path(&graph, s, t);
                    let bidi_ans = ctx.bidirectional_shortest_path(&graph, s, t);

                    assert_eq!(
                        seq_ans, bidi_ans,
                        "Mismatch on query ({} -> {}) in graph with n={}, m={}: seq={}, bidi={}",
                        s, t, n, m, seq_ans, bidi_ans
                    );

                    if seq_ans != -1 {
                        assert_eq!(
                            graph.wcc[s as usize], graph.wcc[t as usize],
                            "WCC falsely rejected reachable pair {} -> {}",
                            s, t
                        );
                    }
                }
            }
        }
    }

    // Additional V3 tests for parallel chunking, partition boundaries, empty chunks, and malformed inputs
    #[test]
    fn test_partition_byte_ranges_boundary_alignment() {
        let sample_text = b"0 1 10\n1 2 20\n2 3 30\n3 4 40\n4 5 50\n5 6 60\n";
        let chunks = partition_byte_ranges(sample_text, 3);
        assert_eq!(chunks.len(), 3);
        // Verify concatenation recovers exact byte sequence
        let mut reconstructed = Vec::new();
        for c in chunks {
            assert!(c.is_empty() || c.ends_with(b"\n"), "Chunk must end with newline");
            reconstructed.extend_from_slice(c);
        }
        assert_eq!(reconstructed, sample_text);
    }

    #[test]
    fn test_partition_empty_chunks() {
        let sample_text = b"0 1 10\n";
        let chunks = partition_byte_ranges(sample_text, 4);
        assert_eq!(chunks.len(), 4);
        let non_empty: Vec<&[u8]> = chunks.into_iter().filter(|c| !c.is_empty()).collect();
        assert_eq!(non_empty.len(), 1);
        assert_eq!(non_empty[0], sample_text);
    }

    #[test]
    fn test_duplicate_edges_split_across_chunks() {
        // Parallel edges (0 -> 1) with weights 100, 20, 50 split across lines that will land in different chunks
        let graph_bytes = b"4 6\n\
0 1 100\n\
1 2 5\n\
2 3 10\n\
0 1 20\n\
3 0 15\n\
0 1 50\n";
        let queries_bytes = b"0 1\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"20\n", "Parallel edges across chunks must retain minimum weight 20");
    }

    #[test]
    fn test_self_loops_split_across_chunks() {
        let graph_bytes = b"3 6\n\
0 0 1\n\
0 1 10\n\
1 1 2\n\
1 2 20\n\
2 2 3\n\
0 2 100\n";
        let queries_bytes = b"0 2\n0 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"30\n0\n", "Self-loops in any chunk must be safely ignored");
    }

    #[test]
    fn test_malformed_input_in_parallel_chunk() {
        // Line with out-of-bounds node id in middle chunk
        let graph_bytes = b"4 4\n\
0 1 10\n\
1 2 20\n\
99 3 30\n\
2 3 40\n";
        let res = parse_graph(graph_bytes);
        assert!(res.is_err(), "Out-of-bounds node must return Err");
        let err_msg = res.unwrap_err();
        assert!(err_msg.contains("out of bounds"), "Error message should mention out of bounds: {}", err_msg);
    }
}
