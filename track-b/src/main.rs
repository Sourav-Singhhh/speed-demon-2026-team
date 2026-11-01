use std::env;
use std::fs::File;
use std::io::Write;
use std::thread;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    And,
    Or,
    Not,
}

enum Query {
    Bool {
        terms: Vec<Option<u32>>,
        ops: Vec<Op>,
    },
    Phrase {
        qid: usize,
    },
}

#[derive(Clone)]
struct VocabSlot {
    hash: u64,
    token: Vec<u8>,
    id: u32,
    is_phrase: bool,
}

struct Vocab {
    slots: Vec<VocabSlot>,
    mask: usize,
    count: usize,
}

impl Vocab {
    fn new(cap: usize) -> Self {
        let size = cap.next_power_of_two();
        let mut slots = Vec::with_capacity(size);
        for _ in 0..size {
            slots.push(VocabSlot {
                hash: 0,
                token: Vec::new(),
                id: u32::MAX,
                is_phrase: false,
            });
        }
        Self {
            slots,
            mask: size - 1,
            count: 0,
        }
    }

    #[inline(always)]
    fn hash_bytes(b: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for &byte in b {
            h = (h ^ (byte as u64)).wrapping_mul(0x100000001b3);
        }
        if h == 0 {
            1
        } else {
            h
        }
    }

    fn ensure_capacity(&mut self) {
        if self.count * 2 < self.slots.len() {
            return;
        }
        let old_slots = std::mem::replace(&mut self.slots, Vec::new());
        let new_size = old_slots.len() * 2;
        self.slots = (0..new_size)
            .map(|_| VocabSlot {
                hash: 0,
                token: Vec::new(),
                id: u32::MAX,
                is_phrase: false,
            })
            .collect();
        self.mask = new_size - 1;
        for s in old_slots {
            if s.id != u32::MAX {
                let mut idx = (s.hash as usize) & self.mask;
                while self.slots[idx].id != u32::MAX {
                    idx = (idx + 1) & self.mask;
                }
                self.slots[idx] = s;
            }
        }
    }

    fn get_or_insert(&mut self, token: &[u8], is_phrase: bool) -> u32 {
        self.ensure_capacity();
        let h = Self::hash_bytes(token);
        let mut idx = (h as usize) & self.mask;
        loop {
            let slot = &mut self.slots[idx];
            if slot.id == u32::MAX {
                let new_id = self.count as u32;
                *slot = VocabSlot {
                    hash: h,
                    token: token.to_vec(),
                    id: new_id,
                    is_phrase,
                };
                self.count += 1;
                return new_id;
            }
            if slot.hash == h && slot.token == token {
                if is_phrase {
                    slot.is_phrase = true;
                }
                return slot.id;
            }
            idx = (idx + 1) & self.mask;
        }
    }

    #[inline(always)]
    fn lookup(&self, token: &[u8]) -> Option<(u32, bool)> {
        let h = Self::hash_bytes(token);
        let mut idx = (h as usize) & self.mask;
        loop {
            let slot = &self.slots[idx];
            if slot.id == u32::MAX {
                return None;
            }
            if slot.hash == h && slot.token == token {
                return Some((slot.id, slot.is_phrase));
            }
            idx = (idx + 1) & self.mask;
        }
    }
}

// Compact Phrase Trie
struct TrieNode {
    edges_start: u32,
    edges_len: u16,
    matches_start: u32,
    matches_len: u16,
}

struct TrieEdge {
    tok_id: u32,
    next_node: u32,
}

struct PhraseTrie {
    root_table: Vec<u32>, // direct lookup for root transitions: tok_id -> node_idx
    nodes: Vec<TrieNode>,
    edges: Vec<TrieEdge>,
    matches: Vec<u32>,
}

impl PhraseTrie {
    fn new(num_tokens: usize) -> Self {
        Self {
            root_table: vec![0; num_tokens],
            nodes: Vec::new(),
            edges: Vec::new(),
            matches: Vec::new(),
        }
    }

    #[inline(always)]
    fn step(&self, node_idx: usize, tok_id: u32) -> u32 {
        if node_idx == 0 {
            if (tok_id as usize) < self.root_table.len() {
                return self.root_table[tok_id as usize];
            }
            return 0;
        }
        let node = &self.nodes[node_idx];
        let start = node.edges_start as usize;
        let end = start + node.edges_len as usize;
        for i in start..end {
            if self.edges[i].tok_id == tok_id {
                return self.edges[i].next_node;
            }
        }
        0
    }
}

// Fast ASCII Tokenizer
struct TokenIter<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> TokenIter<'a> {
    #[inline(always)]
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = &'a [u8];

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let len = self.bytes.len();
        while self.pos < len {
            let b = self.bytes[self.pos];
            if (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'Z') {
                break;
            }
            self.pos += 1;
        }
        if self.pos >= len {
            return None;
        }
        let start = self.pos;
        while self.pos < len {
            let b = self.bytes[self.pos];
            if (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'Z') {
                self.pos += 1;
            } else {
                break;
            }
        }
        Some(&self.bytes[start..self.pos])
    }
}

#[inline(always)]
fn lower_token(dst: &mut [u8; 32], src: &[u8]) -> usize {
    let len = src.len().min(32);
    for i in 0..len {
        let b = src[i];
        dst[i] = if b >= b'A' && b <= b'Z' { b + 32 } else { b };
    }
    len
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: solution <data_dir> <out_dir>");
        std::process::exit(1);
    }
    let data_dir = &args[1];
    let out_dir = &args[2];
    let docs_path = format!("{}/docs.txt", data_dir);
    let queries_path = format!("{}/queries.txt", data_dir);
    let out_path = format!("{}/results.txt", out_dir);

    // 1. Read queries.txt
    let queries_content = match std::fs::read(&queries_path) {
        Ok(c) => c,
        Err(_) => {
            let _ = File::create(&out_path);
            return;
        }
    };

    let mut vocab = Vocab::new(262144);
    let mut parsed_queries = Vec::with_capacity(50000);
    let mut raw_phrases = Vec::new();

    let mut q_idx = 0;
    for raw_line in queries_content.split(|&b| b == b'\n') {
        let line = if raw_line.ends_with(b"\r") {
            &raw_line[..raw_line.len() - 1]
        } else {
            raw_line
        };
        if line.is_empty() {
            continue;
        }
        if line.starts_with(b"BOOL ") {
            let parts: Vec<&[u8]> = line[5..].split(|&b| b == b' ').collect();
            let mut terms = Vec::new();
            let mut ops = Vec::new();
            let mut i = 0;
            while i < parts.len() {
                let tid = vocab.get_or_insert(parts[i], false);
                terms.push(Some(tid));
                i += 1;
                if i < parts.len() {
                    let op = match parts[i] {
                        b"AND" => Op::And,
                        b"OR" => Op::Or,
                        b"NOT" => Op::Not,
                        _ => Op::And,
                    };
                    ops.push(op);
                    i += 1;
                }
            }
            parsed_queries.push(Query::Bool { terms, ops });
        } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") {
            let inner = &line[8..line.len() - 1];
            let parts: Vec<&[u8]> = inner.split(|&b| b == b' ').collect();
            let mut term_ids = Vec::with_capacity(parts.len());
            for p in parts {
                term_ids.push(vocab.get_or_insert(p, true));
            }
            raw_phrases.push((q_idx, term_ids));
            parsed_queries.push(Query::Phrase { qid: q_idx });
        }
        q_idx += 1;
    }

    let num_vocab = vocab.count;
    let num_queries = q_idx;

    // 2. Build Phrase Trie
    let mut temp_trie_edges: Vec<Vec<(u32, u32)>> = vec![Vec::new()];
    let mut temp_trie_matches: Vec<Vec<u32>> = vec![Vec::new()];

    for &(qid, ref tids) in &raw_phrases {
        let mut curr = 0usize;
        for &tid in tids {
            let mut found = None;
            for &(edge_tid, next_node) in &temp_trie_edges[curr] {
                if edge_tid == tid {
                    found = Some(next_node as usize);
                    break;
                }
            }
            curr = match found {
                Some(next) => next,
                None => {
                    let new_node = temp_trie_edges.len();
                    temp_trie_edges.push(Vec::new());
                    temp_trie_matches.push(Vec::new());
                    temp_trie_edges[curr].push((tid, new_node as u32));
                    new_node
                }
            };
        }
        temp_trie_matches[curr].push(qid as u32);
    }

    let mut phrase_trie = PhraseTrie::new(num_vocab);
    let mut node_edges_start = Vec::with_capacity(temp_trie_edges.len());
    let mut flat_edges = Vec::new();

    for (node_idx, edges) in temp_trie_edges.iter().enumerate() {
        let start = flat_edges.len() as u32;
        node_edges_start.push(start);
        for &(tid, next_node) in edges {
            flat_edges.push(TrieEdge {
                tok_id: tid,
                next_node,
            });
            if node_idx == 0 && (tid as usize) < phrase_trie.root_table.len() {
                phrase_trie.root_table[tid as usize] = next_node;
            }
        }
    }

    let mut flat_matches = Vec::new();
    for (node_idx, edges) in temp_trie_edges.into_iter().enumerate() {
        let m_start = flat_matches.len() as u32;
        let m_len = temp_trie_matches[node_idx].len() as u16;
        flat_matches.extend_from_slice(&temp_trie_matches[node_idx]);

        phrase_trie.nodes.push(TrieNode {
            edges_start: node_edges_start[node_idx],
            edges_len: edges.len() as u16,
            matches_start: m_start,
            matches_len: m_len,
        });
    }
    phrase_trie.edges = flat_edges;
    phrase_trie.matches = flat_matches;

    // 3. Open and mmap docs.txt
    let docs_mmap = unsafe {
        let f = match File::open(&docs_path) {
            Ok(file) => file,
            Err(_) => {
                let _ = File::create(&out_path);
                return;
            }
        };
        match memmap2_minimal(&f) {
            Some(m) => m,
            None => {
                let _ = File::create(&out_path);
                return;
            }
        }
    };

    if docs_mmap.is_empty() {
        let mut out_file = File::create(&out_path).unwrap();
        for _ in 0..parsed_queries.len() {
            let _ = out_file.write_all(b"0 0\n");
        }
        return;
    }

    // Parallel chunk execution
    let num_threads = 4.min(
        thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4),
    );
    let chunk_size = docs_mmap.len() / num_threads;

    let mut chunk_boundaries = vec![0; num_threads + 1];
    for t in 1..num_threads {
        let mut split = t * chunk_size;
        while split < docs_mmap.len() && docs_mmap[split] != b'\n' {
            split += 1;
        }
        if split < docs_mmap.len() {
            split += 1;
        }
        chunk_boundaries[t] = split;
    }
    chunk_boundaries[num_threads] = docs_mmap.len();

    let thread_results = thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_threads);
        for t in 0..num_threads {
            let start = chunk_boundaries[t];
            let end = chunk_boundaries[t + 1];
            let vocab_ref = &vocab;
            let trie_ref = &phrase_trie;
            let m_ref = &docs_mmap[..];

            handles.push(s.spawn(move || {
                let mut local_postings: Vec<Vec<u32>> =
                    (0..num_vocab).map(|_| Vec::new()).collect();
                let mut local_phrase_results: Vec<Vec<u32>> =
                    (0..num_queries).map(|_| Vec::new()).collect();
                let mut last_seen = vec![u32::MAX; num_vocab];
                let mut phrase_last_seen = vec![u32::MAX; num_queries];
                let mut tok_buf = [0u8; 32];
                let mut active_states = [0u32; 16];
                let mut next_states = [0u32; 16];

                let mut pos = start;
                while pos < end {
                    let mut doc_id: u32 = 0;
                    while pos < end && m_ref[pos] != b'\t' {
                        if m_ref[pos] >= b'0' && m_ref[pos] <= b'9' {
                            doc_id = doc_id * 10 + (m_ref[pos] - b'0') as u32;
                        }
                        pos += 1;
                    }
                    if pos >= end {
                        break;
                    }
                    pos += 1; // skip TAB
                    let text_start = pos;
                    while pos < end && m_ref[pos] != b'\n' {
                        pos += 1;
                    }
                    let text_end = pos;
                    if pos < end {
                        pos += 1;
                    }

                    let text = &m_ref[text_start..text_end];
                    let mut iter = TokenIter::new(text);
                    let mut num_active = 0;

                    while let Some(raw_tok) = iter.next() {
                        let len = lower_token(&mut tok_buf, raw_tok);
                        if let Some((tid, is_phrase)) = vocab_ref.lookup(&tok_buf[..len]) {
                            let t_idx = tid as usize;
                            if last_seen[t_idx] != doc_id {
                                last_seen[t_idx] = doc_id;
                                local_postings[t_idx].push(doc_id);
                            }

                            if is_phrase {
                                let mut num_next = 0;
                                for i in 0..num_active {
                                    let next_s = trie_ref.step(active_states[i] as usize, tid);
                                    if next_s != 0 {
                                        let node = &trie_ref.nodes[next_s as usize];
                                        if node.matches_len > 0 {
                                            let m_start = node.matches_start as usize;
                                            let m_end = m_start + node.matches_len as usize;
                                            for &qid in &trie_ref.matches[m_start..m_end] {
                                                let q_idx = qid as usize;
                                                if phrase_last_seen[q_idx] != doc_id {
                                                    phrase_last_seen[q_idx] = doc_id;
                                                    local_phrase_results[q_idx].push(doc_id);
                                                }
                                            }
                                        }
                                        if num_next < 15
                                            && !next_states[..num_next].contains(&next_s)
                                        {
                                            next_states[num_next] = next_s;
                                            num_next += 1;
                                        }
                                    }
                                }
                                let root_next = trie_ref.step(0, tid);
                                if root_next != 0 {
                                    let node = &trie_ref.nodes[root_next as usize];
                                    if node.matches_len > 0 {
                                        let m_start = node.matches_start as usize;
                                        let m_end = m_start + node.matches_len as usize;
                                        for &qid in &trie_ref.matches[m_start..m_end] {
                                            let q_idx = qid as usize;
                                            if phrase_last_seen[q_idx] != doc_id {
                                                phrase_last_seen[q_idx] = doc_id;
                                                local_phrase_results[q_idx].push(doc_id);
                                            }
                                        }
                                    }
                                    if num_next < 16
                                        && !next_states[..num_next].contains(&root_next)
                                    {
                                        next_states[num_next] = root_next;
                                        num_next += 1;
                                    }
                                }
                                num_active = num_next;
                                for i in 0..num_active {
                                    active_states[i] = next_states[i];
                                }
                            } else {
                                num_active = 0;
                            }
                        } else {
                            num_active = 0;
                        }
                    }
                }
                (local_postings, local_phrase_results)
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });

    // Merge thread postings and phrase matches
    let mut postings: Vec<Vec<u32>> = (0..num_vocab).map(|_| Vec::new()).collect();
    let mut phrase_results: Vec<Vec<u32>> = (0..num_queries).map(|_| Vec::new()).collect();

    for (t_postings, t_phrases) in thread_results {
        for (tid, p_list) in t_postings.into_iter().enumerate() {
            postings[tid].extend_from_slice(&p_list);
        }
        for (qid, m_list) in t_phrases.into_iter().enumerate() {
            phrase_results[qid].extend_from_slice(&m_list);
        }
    }

    // 4. Evaluate BOOL queries with reusable scratch buffers and format output
    let mut out_file = File::create(&out_path).unwrap();
    let mut out_buf = Vec::with_capacity(512 * 1024);
    let mut buf_a = Vec::with_capacity(250000);
    let mut buf_b = Vec::with_capacity(250000);

    for query in parsed_queries {
        match query {
            Query::Bool { terms, ops } => {
                if terms.is_empty() {
                    out_buf.extend_from_slice(b"0 0\n");
                    continue;
                }
                buf_a.clear();
                if let Some(tid) = terms[0] {
                    buf_a.extend_from_slice(&postings[tid as usize]);
                }

                for (i, &op) in ops.iter().enumerate() {
                    let next_postings = match terms[i + 1] {
                        Some(tid) => &postings[tid as usize][..],
                        None => &[][..],
                    };
                    buf_b.clear();
                    match op {
                        Op::And => intersect_into(&buf_a, next_postings, &mut buf_b),
                        Op::Or => union_into(&buf_a, next_postings, &mut buf_b),
                        Op::Not => difference_into(&buf_a, next_postings, &mut buf_b),
                    }
                    std::mem::swap(&mut buf_a, &mut buf_b);
                }

                write_result(&mut out_buf, &buf_a);
            }
            Query::Phrase { qid } => {
                let matches = &phrase_results[qid];
                write_result(&mut out_buf, matches);
            }
        }

        if out_buf.len() >= 256 * 1024 {
            out_file.write_all(&out_buf).unwrap();
            out_buf.clear();
        }
    }

    if !out_buf.is_empty() {
        out_file.write_all(&out_buf).unwrap();
    }
}

#[inline(always)]
fn intersect_into(a: &[u32], b: &[u32], out: &mut Vec<u32>) {
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        if a[i] == b[j] {
            out.push(a[i]);
            i += 1;
            j += 1;
        } else if a[i] < b[j] {
            i += 1;
        } else {
            j += 1;
        }
    }
}

#[inline(always)]
fn union_into(a: &[u32], b: &[u32], out: &mut Vec<u32>) {
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        if a[i] == b[j] {
            out.push(a[i]);
            i += 1;
            j += 1;
        } else if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else {
            out.push(b[j]);
            j += 1;
        }
    }
    while i < a.len() {
        out.push(a[i]);
        i += 1;
    }
    while j < b.len() {
        out.push(b[j]);
        j += 1;
    }
}

#[inline(always)]
fn difference_into(a: &[u32], b: &[u32], out: &mut Vec<u32>) {
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        if a[i] == b[j] {
            i += 1;
            j += 1;
        } else if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else {
            j += 1;
        }
    }
    while i < a.len() {
        out.push(a[i]);
        i += 1;
    }
}

#[inline(always)]
fn write_result(buf: &mut Vec<u8>, docs: &[u32]) {
    let cnt = docs.len();
    if cnt == 0 {
        buf.extend_from_slice(b"0 0\n");
        return;
    }
    let mut sum: u64 = 0;
    for &d in docs {
        sum += d as u64;
    }
    itoa(buf, cnt as u64);
    buf.push(b' ');
    itoa(buf, sum);

    let m = cnt.min(10);
    for i in 0..m {
        buf.push(b' ');
        itoa(buf, docs[i] as u64);
    }
    buf.push(b'\n');
}

#[inline(always)]
fn itoa(buf: &mut Vec<u8>, mut n: u64) {
    if n == 0 {
        buf.push(b'0');
        return;
    }
    let mut temp = [0u8; 20];
    let mut i = 0;
    while n > 0 {
        temp[i] = b'0' + (n % 10) as u8;
        n /= 10;
        i += 1;
    }
    while i > 0 {
        i -= 1;
        buf.push(temp[i]);
    }
}

// Minimal POSIX mmap implementation without third-party crates
#[cfg(unix)]
unsafe fn memmap2_minimal(file: &File) -> Option<&'static [u8]> {
    use std::os::unix::io::AsRawFd;
    let len = file.metadata().ok()?.len() as usize;
    if len == 0 {
        return Some(&[]);
    }
    let ptr = libc_mmap(len, file.as_raw_fd());
    if ptr.is_null() {
        None
    } else {
        Some(std::slice::from_raw_parts(ptr as *const u8, len))
    }
}

#[cfg(windows)]
unsafe fn memmap2_minimal(file: &File) -> Option<&'static [u8]> {
    use std::io::Read;
    let mut f = file;
    let mut v = Vec::new();
    f.read_to_end(&mut v).ok()?;
    Some(Box::leak(v.into_boxed_slice()))
}

#[cfg(unix)]
unsafe fn libc_mmap(len: usize, fd: i32) -> *mut u8 {
    extern "C" {
        fn mmap(
            addr: *mut std::ffi::c_void,
            len: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut std::ffi::c_void;
    }
    const PROT_READ: i32 = 1;
    const MAP_PRIVATE: i32 = 2;
    let ptr = mmap(std::ptr::null_mut(), len, PROT_READ, MAP_PRIVATE, fd, 0);
    if ptr == usize::MAX as *mut std::ffi::c_void {
        std::ptr::null_mut()
    } else {
        ptr as *mut u8
    }
}
