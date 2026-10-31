use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::env;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering as AtomicOrdering};

#[cfg(target_os = "linux")]
fn mmap_file(file: &fs::File, len: usize) -> Result<&'static [u8], String> {
    use std::os::unix::io::AsRawFd;
    if len == 0 { return Ok(&[]); }
    let fd = file.as_raw_fd();
    let addr: *mut u8;
    unsafe {
        std::arch::asm!(
            "syscall",
            in("rax") 9usize, in("rdi") 0usize, in("rsi") len,
            in("rdx") 1usize, in("r10") 2usize, in("r8") fd, in("r9") 0usize,
            lateout("rax") addr, lateout("rcx") _, lateout("r11") _,
        );
    }
    if (addr as isize) < 0 && (addr as isize) > -4096 {
        return Err(format!("mmap errno {}", -(addr as isize)));
    }
    unsafe { Ok(std::slice::from_raw_parts(addr, len)) }
}

#[cfg(not(target_os = "linux"))]
fn mmap_file(_file: &fs::File, _len: usize) -> Result<&'static [u8], String> {
    Err("mmap linux only".to_string())
}

fn load_input(path: &Path) -> &'static [u8] {
    let file = fs::File::open(path).expect("open failed");
    let len = file.metadata().expect("meta failed").len() as usize;
    if let Ok(mapped) = mmap_file(&file, len) {
        mapped
    } else {
        Box::leak(fs::read(path).expect("read failed").into_boxed_slice())
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    cost: u64,
    node: u32,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost).then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[inline(always)]
fn parse_u32(bytes: &[u8], pos: &mut usize) -> u32 {
    while *pos < bytes.len() && bytes[*pos] <= b' ' {
        *pos += 1;
    }
    let mut val = 0u32;
    while *pos < bytes.len() && bytes[*pos] >= b'0' && bytes[*pos] <= b'9' {
        val = val * 10 + (bytes[*pos] - b'0') as u32;
        *pos += 1;
    }
    val
}

#[inline(always)]
fn write_i64(buf: &mut Vec<u8>, mut n: i64) {
    if n < 0 {
        buf.push(b'-');
        n = -n;
    }
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

fn partition_byte_ranges(data: &[u8], num_chunks: usize) -> Vec<&[u8]> {
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
            b += 1;
        }
        boundaries.push(b.min(total_len));
    }
    boundaries.push(total_len);

    let mut chunks = Vec::with_capacity(num_chunks);
    for i in 0..num_chunks {
        let start = boundaries[i];
        let end = boundaries[i + 1];
        if start < end {
            chunks.push(&data[start..end]);
        }
    }
    chunks
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let graph_bytes = load_input(&Path::new(data_dir).join("graph.txt"));
    let query_bytes = load_input(&Path::new(data_dir).join("queries.txt"));

    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(4));

    let mut pos = 0;
    let n = parse_u32(graph_bytes, &mut pos) as usize;
    let m = parse_u32(graph_bytes, &mut pos) as usize;
    while pos < graph_bytes.len() && graph_bytes[pos] <= b' ' {
        pos += 1;
    }

    let edge_bytes = &graph_bytes[pos..];
    let chunks = partition_byte_ranges(edge_bytes, num_threads);

    let f_deg_atomic = (0..n).map(|_| AtomicU32::new(0)).collect::<Vec<_>>();
    let b_deg_atomic = (0..n).map(|_| AtomicU32::new(0)).collect::<Vec<_>>();

    // PASS 1: Parallel count degrees
    std::thread::scope(|s| {
        for chunk in &chunks {
            let fd = &f_deg_atomic;
            let bd = &b_deg_atomic;
            s.spawn(move || {
                let mut p = 0;
                while p < chunk.len() {
                    while p < chunk.len() && chunk[p] <= b' ' { p += 1; }
                    if p >= chunk.len() { break; }
                    let u = parse_u32(chunk, &mut p) as usize;
                    let v = parse_u32(chunk, &mut p) as usize;
                    let _w = parse_u32(chunk, &mut p);
                    if u < n && v < n {
                        fd[u].fetch_add(1, AtomicOrdering::Relaxed);
                        bd[v].fetch_add(1, AtomicOrdering::Relaxed);
                    }
                }
            });
        }
    });

    let mut f_offsets = vec![0u32; n + 1];
    let mut b_offsets = vec![0u32; n + 1];
    let mut f_cur = 0u32;
    let mut b_cur = 0u32;
    for i in 0..n {
        f_offsets[i] = f_cur;
        f_cur += f_deg_atomic[i].load(AtomicOrdering::Relaxed);
        b_offsets[i] = b_cur;
        b_cur += b_deg_atomic[i].load(AtomicOrdering::Relaxed);
    }
    f_offsets[n] = f_cur;
    b_offsets[n] = b_cur;
    drop(f_deg_atomic);
    drop(b_deg_atomic);

    let mut f_edges = vec![0u64; m];
    let mut b_edges = vec![0u64; m];

    let f_cur_offsets = f_offsets[..n].iter().map(|&o| AtomicU32::new(o)).collect::<Vec<_>>();
    let b_cur_offsets = b_offsets[..n].iter().map(|&o| AtomicU32::new(o)).collect::<Vec<_>>();

    let f_edges_ptr = f_edges.as_mut_ptr() as usize;
    let b_edges_ptr = b_edges.as_mut_ptr() as usize;

    // PASS 2: Parallel scatter edges into CSR
    std::thread::scope(|s| {
        for chunk in &chunks {
            let f_cur = &f_cur_offsets;
            let b_cur = &b_cur_offsets;
            s.spawn(move || {
                let f_e = f_edges_ptr as *mut u64;
                let b_e = b_edges_ptr as *mut u64;

                let mut p = 0;
                while p < chunk.len() {
                    while p < chunk.len() && chunk[p] <= b' ' { p += 1; }
                    if p >= chunk.len() { break; }
                    let u = parse_u32(chunk, &mut p);
                    let v = parse_u32(chunk, &mut p);
                    let w = parse_u32(chunk, &mut p);

                    if (u as usize) < n && (v as usize) < n {
                        let f_dst = f_cur[u as usize].fetch_add(1, AtomicOrdering::Relaxed) as usize;
                        let b_dst = b_cur[v as usize].fetch_add(1, AtomicOrdering::Relaxed) as usize;
                        unsafe {
                            *f_e.add(f_dst) = ((v as u64) << 32) | (w as u64);
                            *b_e.add(b_dst) = ((u as u64) << 32) | (w as u64);
                        }
                    }
                }
            });
        }
    });
    drop(f_cur_offsets);
    drop(b_cur_offsets);

    // Fast sequential DSU over populated forward edges (takes ~15ms)
    let mut dsu_parent: Vec<u32> = (0..n as u32).collect();
    let mut dsu_rank = vec![0u8; n];
    for u in 0..n {
        let start = f_offsets[u] as usize;
        let end = f_offsets[u + 1] as usize;
        for i in start..end {
            let v = (f_edges[i] >> 32) as usize;
            let mut ra = u as u32;
            while ra != dsu_parent[ra as usize] { ra = dsu_parent[ra as usize]; }
            let mut rb = v as u32;
            while rb != dsu_parent[rb as usize] { rb = dsu_parent[rb as usize]; }
            if ra != rb {
                if dsu_rank[ra as usize] < dsu_rank[rb as usize] {
                    dsu_parent[ra as usize] = rb;
                } else if dsu_rank[ra as usize] > dsu_rank[rb as usize] {
                    dsu_parent[rb as usize] = ra;
                } else {
                    dsu_parent[rb as usize] = ra;
                    dsu_rank[ra as usize] += 1;
                }
            }
        }
    }
    drop(dsu_rank);

    // Flatten DSU roots in-place -> wcc array
    for i in 0..n {
        let mut r = i as u32;
        while r != dsu_parent[r as usize] { r = dsu_parent[r as usize]; }
        let mut cur = i as u32;
        while cur != r {
            let nxt = dsu_parent[cur as usize];
            dsu_parent[cur as usize] = r;
            cur = nxt;
        }
    }
    let wcc = dsu_parent;

    // Parse queries
    let mut queries = Vec::with_capacity(2048);
    let mut p = 0;
    while p < query_bytes.len() {
        while p < query_bytes.len() && query_bytes[p] <= b' ' {
            p += 1;
        }
        if p >= query_bytes.len() {
            break;
        }
        let s = parse_u32(query_bytes, &mut p);
        let t = parse_u32(query_bytes, &mut p);
        queries.push((s, t));
    }

    let q_count = queries.len();
    let mut answers = vec![0i64; q_count];
    let next_query_idx = AtomicUsize::new(0);
    let answers_ptr = answers.as_mut_ptr() as usize;

    let num_words = (n + 63) / 64;

    std::thread::scope(|s| {
        for _ in 0..num_threads {
            let next_idx = &next_query_idx;
            let q_ref = &queries;
            let f_offs = &f_offsets;
            let f_ed = &f_edges;
            let b_offs = &b_offsets;
            let b_ed = &b_edges;
            let wcc_ref = &wcc;

            s.spawn(move || {
                let ans_base = answers_ptr as *mut i64;
                let mut dist_f = vec![u64::MAX; n];
                let mut dist_b = vec![u64::MAX; n];
                let mut settled_f_words = vec![0u64; num_words];
                let mut settled_b_words = vec![0u64; num_words];
                let mut visited_f = Vec::with_capacity(1024);
                let mut visited_b = Vec::with_capacity(1024);
                let mut settled_nodes_f = Vec::with_capacity(512);
                let mut settled_nodes_b = Vec::with_capacity(512);
                let mut heap_f = BinaryHeap::with_capacity(2048);
                let mut heap_b = BinaryHeap::with_capacity(2048);

                loop {
                    let q_idx = next_idx.fetch_add(1, AtomicOrdering::Relaxed);
                    if q_idx >= q_count {
                        break;
                    }
                    let (s_node, t_node) = q_ref[q_idx];

                    if s_node == t_node {
                        unsafe { *ans_base.add(q_idx) = 0; }
                        continue;
                    }

                    let s_idx = s_node as usize;
                    let t_idx = t_node as usize;

                    // O(1) early unreachable pruning: different WCC or zero degree
                    if wcc_ref[s_idx] != wcc_ref[t_idx]
                        || f_offs[s_idx + 1] == f_offs[s_idx]
                        || b_offs[t_idx + 1] == b_offs[t_idx]
                    {
                        unsafe { *ans_base.add(q_idx) = -1; }
                        continue;
                    }

                    // Reset visited distances & settled bitsets
                    for &node in &visited_f {
                        dist_f[node as usize] = u64::MAX;
                    }
                    visited_f.clear();

                    for &node in &visited_b {
                        dist_b[node as usize] = u64::MAX;
                    }
                    visited_b.clear();

                    for &node in &settled_nodes_f {
                        let idx = node as usize;
                        settled_f_words[idx >> 6] &= !(1u64 << (idx & 63));
                    }
                    settled_nodes_f.clear();

                    for &node in &settled_nodes_b {
                        let idx = node as usize;
                        settled_b_words[idx >> 6] &= !(1u64 << (idx & 63));
                    }
                    settled_nodes_b.clear();

                    heap_f.clear();
                    heap_b.clear();

                    dist_f[s_idx] = 0;
                    visited_f.push(s_node);
                    heap_f.push(State { cost: 0, node: s_node });

                    dist_b[t_idx] = 0;
                    visited_b.push(t_node);
                    heap_b.push(State { cost: 0, node: t_node });

                    let mut mu = u64::MAX;

                    loop {
                        let top_f = heap_f.peek().map(|s| s.cost);
                        let top_b = heap_b.peek().map(|s| s.cost);

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
                            let State { cost, node } = heap_f.pop().unwrap();
                            let u_idx = node as usize;
                            if cost > dist_f[u_idx] {
                                continue;
                            }
                            if (settled_f_words[u_idx >> 6] & (1u64 << (u_idx & 63))) != 0 {
                                continue;
                            }
                            settled_f_words[u_idx >> 6] |= 1u64 << (u_idx & 63);
                            settled_nodes_f.push(node);

                            if dist_b[u_idx] != u64::MAX {
                                mu = mu.min(cost.saturating_add(dist_b[u_idx]));
                            }

                            let e_start = f_offs[u_idx] as usize;
                            let e_end = f_offs[u_idx + 1] as usize;
                            for i in e_start..e_end {
                                let edge = f_ed[i];
                                let v = (edge >> 32) as u32;
                                let next_cost = cost.saturating_add((edge as u32) as u64);
                                let v_idx = v as usize;

                                if dist_f[v_idx] == u64::MAX {
                                    visited_f.push(v);
                                    dist_f[v_idx] = next_cost;
                                    heap_f.push(State { cost: next_cost, node: v });
                                    if dist_b[v_idx] != u64::MAX {
                                        mu = mu.min(next_cost.saturating_add(dist_b[v_idx]));
                                    }
                                } else if next_cost < dist_f[v_idx] {
                                    dist_f[v_idx] = next_cost;
                                    heap_f.push(State { cost: next_cost, node: v });
                                    if dist_b[v_idx] != u64::MAX {
                                        mu = mu.min(next_cost.saturating_add(dist_b[v_idx]));
                                    }
                                }
                            }
                        } else {
                            let State { cost, node } = heap_b.pop().unwrap();
                            let v_idx = node as usize;
                            if cost > dist_b[v_idx] {
                                continue;
                            }
                            if (settled_b_words[v_idx >> 6] & (1u64 << (v_idx & 63))) != 0 {
                                continue;
                            }
                            settled_b_words[v_idx >> 6] |= 1u64 << (v_idx & 63);
                            settled_nodes_b.push(node);

                            if dist_f[v_idx] != u64::MAX {
                                mu = mu.min(cost.saturating_add(dist_f[v_idx]));
                            }

                            let e_start = b_offs[v_idx] as usize;
                            let e_end = b_offs[v_idx + 1] as usize;
                            for i in e_start..e_end {
                                let edge = b_ed[i];
                                let u = (edge >> 32) as u32;
                                let next_cost = cost.saturating_add((edge as u32) as u64);
                                let u_idx = u as usize;

                                if dist_b[u_idx] == u64::MAX {
                                    visited_b.push(u);
                                    dist_b[u_idx] = next_cost;
                                    heap_b.push(State { cost: next_cost, node: u });
                                    if dist_f[u_idx] != u64::MAX {
                                        mu = mu.min(next_cost.saturating_add(dist_f[u_idx]));
                                    }
                                } else if next_cost < dist_b[u_idx] {
                                    dist_b[u_idx] = next_cost;
                                    heap_b.push(State { cost: next_cost, node: u });
                                    if dist_f[u_idx] != u64::MAX {
                                        mu = mu.min(next_cost.saturating_add(dist_f[u_idx]));
                                    }
                                }
                            }
                        }
                    }

                    let ans = if mu == u64::MAX { -1 } else { mu as i64 };
                    unsafe { *ans_base.add(q_idx) = ans; }
                }
            });
        }
    });

    let mut out_buf = Vec::with_capacity(32 * 1024);
    for ans in answers {
        write_i64(&mut out_buf, ans);
        out_buf.push(b'\n');
    }

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed out dir");
    let out_file_path = out_dir_path.join("distances.txt");
    fs::write(out_file_path, out_buf).expect("failed write distances.txt");

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

    #[test]
    fn test_parse() {
        let b = b"  123 456 ";
        let mut p = 0;
        assert_eq!(parse_u32(b, &mut p), 123);
        assert_eq!(parse_u32(b, &mut p), 456);
    }
}
