use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    cost: u64,
    node: u32,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        // Min-heap: reverse order on cost
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

pub struct CsrGraph {
    pub num_nodes: u32,
    pub raw_edge_count: usize,
    pub retained_edge_count: usize,
    // Forward CSR
    pub offsets: Vec<u32>,
    pub head: Vec<u32>,
    pub weight: Vec<u32>,
    // Backward CSR
    pub rev_offsets: Vec<u32>,
    pub rev_head: Vec<u32>,
    pub rev_weight: Vec<u32>,
    // Degrees
    pub in_degrees: Vec<u32>,
    pub out_degrees: Vec<u32>,
    // Weakly Connected Components
    pub wcc: Vec<u32>,
}

impl CsrGraph {
    #[inline]
    pub fn out_deg(&self, u: u32) -> u32 {
        if (u as usize) < self.out_degrees.len() {
            self.out_degrees[u as usize]
        } else {
            0
        }
    }

    #[inline]
    pub fn in_deg(&self, v: u32) -> u32 {
        if (v as usize) < self.in_degrees.len() {
            self.in_degrees[v as usize]
        } else {
            0
        }
    }

    #[inline]
    pub fn neighbors(&self, u: u32) -> impl Iterator<Item = (u32, u32)> + '_ {
        let u_idx = u as usize;
        let start = self.offsets[u_idx] as usize;
        let end = self.offsets[u_idx + 1] as usize;
        self.head[start..end]
            .iter()
            .copied()
            .zip(self.weight[start..end].iter().copied())
    }

    #[inline]
    pub fn rev_neighbors(&self, v: u32) -> impl Iterator<Item = (u32, u32)> + '_ {
        let v_idx = v as usize;
        let start = self.rev_offsets[v_idx] as usize;
        let end = self.rev_offsets[v_idx + 1] as usize;
        self.rev_head[start..end]
            .iter()
            .copied()
            .zip(self.rev_weight[start..end].iter().copied())
    }
}

struct FastParser<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> FastParser<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    #[inline]
    fn skip_whitespace(&mut self) {
        while self.pos < self.data.len() && self.data[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    #[inline]
    fn parse_u32(&mut self) -> Result<u32, String> {
        self.skip_whitespace();
        if self.pos >= self.data.len() {
            return Err("unexpected EOF parsing u32".to_string());
        }
        let start = self.pos;
        let mut val: u32 = 0;
        while self.pos < self.data.len() && self.data[self.pos].is_ascii_digit() {
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
    fn parse_u64(&mut self) -> Result<u64, String> {
        self.skip_whitespace();
        if self.pos >= self.data.len() {
            return Err("unexpected EOF parsing u64".to_string());
        }
        let start = self.pos;
        let mut val: u64 = 0;
        while self.pos < self.data.len() && self.data[self.pos].is_ascii_digit() {
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
    fn has_more(&mut self) -> bool {
        self.skip_whitespace();
        self.pos < self.data.len()
    }
}

struct Dsu {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl Dsu {
    fn new(n: u32) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n as usize],
        }
    }

    fn find(&mut self, mut x: u32) -> u32 {
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

    fn union(&mut self, a: u32, b: u32) {
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

pub fn parse_graph(data: &[u8]) -> Result<CsrGraph, String> {
    let mut parser = FastParser::new(data);
    let n = parser.parse_u32()?;
    let m = parser.parse_u32()? as usize;

    let mut temp_edges: Vec<(u32, u32, u32)> = Vec::with_capacity(m);
    let mut raw_out_degrees = vec![0u32; n as usize];
    let mut dsu = Dsu::new(n);

    for _ in 0..m {
        let u = parser.parse_u32()?;
        let v = parser.parse_u32()?;
        let w = parser.parse_u64()?;

        if u >= n || v >= n {
            return Err(format!("node id out of bounds: u={}, v={}, n={}", u, v, n));
        }
        if w > u32::MAX as u64 {
            return Err(format!("weight exceeds u32::MAX: {}", w));
        }
        let w_u32 = w as u32;

        // Ignore self-loops
        if u != v {
            temp_edges.push((u, v, w_u32));
            raw_out_degrees[u as usize] += 1;
            dsu.union(u, v);
        }
    }

    // Bucket sort edges by u into CSR format
    let mut bucket_offsets = vec![0usize; (n + 1) as usize];
    for u in 0..n {
        bucket_offsets[(u + 1) as usize] =
            bucket_offsets[u as usize] + raw_out_degrees[u as usize] as usize;
    }

    let mut bucket_heads = vec![0u32; temp_edges.len()];
    let mut bucket_weights = vec![0u32; temp_edges.len()];
    let mut cursor = bucket_offsets.clone();

    for &(u, v, w) in &temp_edges {
        let slot = cursor[u as usize];
        bucket_heads[slot] = v;
        bucket_weights[slot] = w;
        cursor[u as usize] += 1;
    }

    // Step 2: For each node u, sort its out-edges by (v, w) and deduplicate parallel edges,
    // retaining min weight for each unique (u, v) pair.
    let mut final_offsets = vec![0u32; (n + 1) as usize];
    let mut final_head = Vec::with_capacity(temp_edges.len());
    let mut final_weight = Vec::with_capacity(temp_edges.len());
    let mut in_degrees = vec![0u32; n as usize];
    let mut final_out_degrees = vec![0u32; n as usize];

    let mut u_adj: Vec<(u32, u32)> = Vec::with_capacity(32);

    for u in 0..n {
        final_offsets[u as usize] = final_head.len() as u32;
        let start = bucket_offsets[u as usize];
        let end = bucket_offsets[(u + 1) as usize];

        if start < end {
            u_adj.clear();
            for i in start..end {
                u_adj.push((bucket_heads[i], bucket_weights[i]));
            }
            u_adj.sort_unstable_by_key(|&(v, w)| (v, w));

            let mut prev_v: Option<u32> = None;
            for &(v, w) in &u_adj {
                if prev_v == Some(v) {
                    continue; // Skip parallel copy with heavier/equal weight
                }
                prev_v = Some(v);
                final_head.push(v);
                final_weight.push(w);
                in_degrees[v as usize] += 1;
                final_out_degrees[u as usize] += 1;
            }
        }
    }
    final_offsets[n as usize] = final_head.len() as u32;

    let retained_edge_count = final_head.len();

    // Step 3: Build Backward CSR from the deduplicated forward edges
    let mut rev_offsets = vec![0u32; (n + 1) as usize];
    for v in 0..n {
        rev_offsets[(v + 1) as usize] = rev_offsets[v as usize] + in_degrees[v as usize];
    }

    let mut rev_head = vec![0u32; retained_edge_count];
    let mut rev_weight = vec![0u32; retained_edge_count];
    let mut rev_cursor = rev_offsets.clone();

    for u in 0..n {
        let start = final_offsets[u as usize] as usize;
        let end = final_offsets[(u + 1) as usize] as usize;
        for i in start..end {
            let v = final_head[i];
            let w = final_weight[i];
            let slot = rev_cursor[v as usize] as usize;
            rev_head[slot] = u;
            rev_weight[slot] = w;
            rev_cursor[v as usize] += 1;
        }
    }

    // Step 4: Extract WCC labels for all nodes
    let mut wcc = vec![0u32; n as usize];
    for u in 0..n {
        wcc[u as usize] = dsu.find(u);
    }

    // Verification check: sum of out_degrees must match retained edge count
    let total_out_deg: u64 = final_out_degrees.iter().map(|&d| d as u64).sum();
    let total_in_deg: u64 = in_degrees.iter().map(|&d| d as u64).sum();
    assert_eq!(
        total_out_deg, retained_edge_count as u64,
        "out_degree sum mismatch"
    );
    assert_eq!(
        total_in_deg, retained_edge_count as u64,
        "in_degree sum mismatch"
    );

    Ok(CsrGraph {
        num_nodes: n,
        raw_edge_count: m,
        retained_edge_count,
        offsets: final_offsets,
        head: final_head,
        weight: final_weight,
        rev_offsets,
        rev_head,
        rev_weight,
        in_degrees,
        out_degrees: final_out_degrees,
        wcc,
    })
}

pub struct DijkstraContext {
    // Forward state
    dist_f: Vec<u64>,
    epoch_f: Vec<u32>,
    settled_f: Vec<u32>,
    // Backward state
    dist_b: Vec<u64>,
    epoch_b: Vec<u32>,
    settled_b: Vec<u32>,
    // Current query epoch
    current_epoch: u32,
    // Heaps
    heap_f: BinaryHeap<State>,
    heap_b: BinaryHeap<State>,
    // Settled counters for benchmarking
    pub total_settled_nodes: usize,
}

impl DijkstraContext {
    pub fn new(num_nodes: u32) -> Self {
        let n = num_nodes as usize;
        Self {
            dist_f: vec![u64::MAX; n],
            epoch_f: vec![0u32; n],
            settled_f: vec![0u32; n],
            dist_b: vec![u64::MAX; n],
            epoch_b: vec![0u32; n],
            settled_b: vec![0u32; n],
            current_epoch: 0,
            heap_f: BinaryHeap::with_capacity(1024),
            heap_b: BinaryHeap::with_capacity(1024),
            total_settled_nodes: 0,
        }
    }

    #[inline]
    fn advance_epoch(&mut self) {
        self.current_epoch = self.current_epoch.wrapping_add(1);
        if self.current_epoch == 0 {
            self.epoch_f.fill(0);
            self.settled_f.fill(0);
            self.epoch_b.fill(0);
            self.settled_b.fill(0);
            self.current_epoch = 1;
        }
    }

    /// Preserved Sequential Dijkstra baseline for reference & differential testing
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

        self.advance_epoch();
        self.heap_f.clear();

        let s_idx = s as usize;
        self.epoch_f[s_idx] = self.current_epoch;
        self.dist_f[s_idx] = 0;
        self.heap_f.push(State { cost: 0, node: s });

        while let Some(State { cost, node }) = self.heap_f.pop() {
            let node_idx = node as usize;
            if cost > self.dist_f[node_idx] {
                continue;
            }
            self.total_settled_nodes += 1;

            if node == t {
                return cost as i64;
            }

            for (v, w) in graph.neighbors(node) {
                let v_idx = v as usize;
                let next_cost = cost.saturating_add(w as u64);

                let is_unvisited = self.epoch_f[v_idx] != self.current_epoch;
                if is_unvisited || next_cost < self.dist_f[v_idx] {
                    self.epoch_f[v_idx] = self.current_epoch;
                    self.dist_f[v_idx] = next_cost;
                    self.heap_f.push(State {
                        cost: next_cost,
                        node: v,
                    });
                }
            }
        }

        -1
    }

    /// Bidirectional Dijkstra with mathematically proven stopping condition
    pub fn bidirectional_shortest_path(&mut self, graph: &CsrGraph, s: u32, t: u32) -> i64 {
        if s == t {
            return 0;
        }
        // WCC filter: if in different undirected components, strictly unreachable
        if graph.wcc[s as usize] != graph.wcc[t as usize] {
            return -1;
        }
        // Degree filters
        if graph.out_deg(s) == 0 || graph.in_deg(t) == 0 {
            return -1;
        }

        self.advance_epoch();
        self.heap_f.clear();
        self.heap_b.clear();

        let s_idx = s as usize;
        self.epoch_f[s_idx] = self.current_epoch;
        self.dist_f[s_idx] = 0;
        self.heap_f.push(State { cost: 0, node: s });

        let t_idx = t as usize;
        self.epoch_b[t_idx] = self.current_epoch;
        self.dist_b[t_idx] = 0;
        self.heap_b.push(State { cost: 0, node: t });

        let mut mu: u64 = u64::MAX;

        loop {
            let top_f = self.heap_f.peek().map(|s| s.cost);
            let top_b = self.heap_b.peek().map(|s| s.cost);

            if top_f.is_none() && top_b.is_none() {
                break;
            }

            // Stopping condition: sum of frontier minima >= best complete path mu
            if let (Some(df), Some(db)) = (top_f, top_b) {
                if df.saturating_add(db) >= mu {
                    break;
                }
            }

            // Alternate frontiers: expand the direction with smaller top key
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
                    continue; // Stale heap entry
                }
                if self.settled_f[node_idx] == self.current_epoch {
                    continue;
                }
                self.settled_f[node_idx] = self.current_epoch;
                self.total_settled_nodes += 1;

                // Check meeting at common vertex
                if self.epoch_b[node_idx] == self.current_epoch {
                    mu = mu.min(cost.saturating_add(self.dist_b[node_idx]));
                }

                // Relax forward out-edges
                for (v, w) in graph.neighbors(node) {
                    let v_idx = v as usize;
                    let next_cost = cost.saturating_add(w as u64);

                    let is_unvisited = self.epoch_f[v_idx] != self.current_epoch;
                    if is_unvisited || next_cost < self.dist_f[v_idx] {
                        self.epoch_f[v_idx] = self.current_epoch;
                        self.dist_f[v_idx] = next_cost;
                        self.heap_f.push(State {
                            cost: next_cost,
                            node: v,
                        });

                        // Check crossing edge into backward frontier
                        if self.epoch_b[v_idx] == self.current_epoch {
                            mu = mu.min(next_cost.saturating_add(self.dist_b[v_idx]));
                        }
                    }
                }
            } else {
                let State { cost, node } = self.heap_b.pop().unwrap();
                let node_idx = node as usize;
                if cost > self.dist_b[node_idx] {
                    continue; // Stale heap entry
                }
                if self.settled_b[node_idx] == self.current_epoch {
                    continue;
                }
                self.settled_b[node_idx] = self.current_epoch;
                self.total_settled_nodes += 1;

                // Check meeting at common vertex
                if self.epoch_f[node_idx] == self.current_epoch {
                    mu = mu.min(self.dist_f[node_idx].saturating_add(cost));
                }

                // Relax backward in-edges (u -> node in original graph)
                for (u, w) in graph.rev_neighbors(node) {
                    let u_idx = u as usize;
                    let next_cost = cost.saturating_add(w as u64);

                    let is_unvisited = self.epoch_b[u_idx] != self.current_epoch;
                    if is_unvisited || next_cost < self.dist_b[u_idx] {
                        self.epoch_b[u_idx] = self.current_epoch;
                        self.dist_b[u_idx] = next_cost;
                        self.heap_b.push(State {
                            cost: next_cost,
                            node: u,
                        });

                        // Check crossing edge into forward frontier
                        if self.epoch_f[u_idx] == self.current_epoch {
                            mu = mu.min(self.dist_f[u_idx].saturating_add(next_cost));
                        }
                    }
                }
            }
        }

        if mu == u64::MAX {
            -1
        } else {
            mu as i64
        }
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

use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

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

    let graph_data = fs::read(&graph_path).expect("failed to read graph.txt");
    let queries_data = fs::read(&queries_path).expect("failed to read queries.txt");

    let graph = parse_graph(&graph_data).expect("graph parse failed");
    eprintln!(
        "Graph parsed: {} nodes, {} raw edges, {} retained edges (deduped)",
        graph.num_nodes, graph.raw_edge_count, graph.retained_edge_count
    );
    let queries = parse_queries(&queries_data).expect("queries parse failed");

    let bench_mode = env::var("BENCH_MODE").unwrap_or_default();
    let num_threads = env::var("NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(12)
                .min(12)
        });

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
        "compare" => {
            // Run Sequential
            let mut seq_ctx = DijkstraContext::new(graph.num_nodes);
            let seq_start = std::time::Instant::now();
            let mut seq_ans = Vec::with_capacity(queries.len());
            for &(s, t) in &queries {
                seq_ans.push(seq_ctx.sequential_shortest_path(&graph, s, t));
            }
            let seq_dur = seq_start.elapsed();

            // Run Single-threaded Bidirectional
            let mut bidi_ctx = DijkstraContext::new(graph.num_nodes);
            let bidi_start = std::time::Instant::now();
            let mut bidi_ans = Vec::with_capacity(queries.len());
            for &(s, t) in &queries {
                bidi_ans.push(bidi_ctx.bidirectional_shortest_path(&graph, s, t));
            }
            let bidi_dur = bidi_start.elapsed();

            // Run Multithreaded Bidirectional
            let mt_start = std::time::Instant::now();
            let (mt_ans, mt_settled) = parallel_bidirectional_traverse(&graph, &queries, num_threads);
            let mt_dur = mt_start.elapsed();

            assert_eq!(seq_ans, bidi_ans, "sequential and bidi_1 differed");
            assert_eq!(bidi_ans, mt_ans, "bidi_1 and bidi_mt differed");

            eprintln!(
                "SIDE-BY-SIDE BENCHMARK ON {} QUERIES:\n  [A] Sequential (1T):    {:?} ({} settled)\n  [B] Bidi (1T):          {:?} ({} settled)\n  [C] Bidi ({}T):         {:?} ({} settled)\n  Bidi/Seq Speedup: {:.2}x\n  MT/Seq Speedup:   {:.2}x\n  MT/Bidi Speedup:  {:.2}x",
                queries.len(),
                seq_dur, seq_ctx.total_settled_nodes,
                bidi_dur, bidi_ctx.total_settled_nodes,
                num_threads, mt_dur, mt_settled,
                seq_dur.as_secs_f64() / bidi_dur.as_secs_f64(),
                seq_dur.as_secs_f64() / mt_dur.as_secs_f64(),
                bidi_dur.as_secs_f64() / mt_dur.as_secs_f64()
            );

            (mt_ans, mt_settled, "Multithreaded Bidirectional Dijkstra", mt_dur)
        }
        _ => {
            // Default production mode: Multithreaded Bidirectional Dijkstra
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

    if let Ok(status) = fs::read_to_string("/proc/self/status") {
        for line in status.lines() {
            if line.starts_with("VmHWM:") {
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
        // Directed triangle: 0 -> 1 (w=2), 1 -> 2 (w=3), 2 -> 0 (w=10)
        // d(0, 2) = 2 + 3 = 5
        // d(2, 0) = 10
        // d(2, 1) = 10 + 2 = 12
        let graph_bytes = b"3 3\n0 1 2\n1 2 3\n2 0 10\n";
        let queries_bytes = b"0 2\n2 0\n2 1\n1 0\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"5\n10\n12\n13\n");
    }

    #[test]
    fn test_multiple_crossing_edges_and_meeting_vertices() {
        // Source 0, target 5.
        // Path A: 0 -> 1 -> 2 -> 5 (weights 1, 10, 1 = 12)
        // Path B: 0 -> 3 -> 4 -> 5 (weights 5, 1, 5 = 11)
        // Path C: direct 0 -> 5 (weight 20)
        // Crossing edge between paths: 1 -> 4 (weight 2) => 0 -> 1 -> 4 -> 5 (1 + 2 + 5 = 8)
        let graph_bytes = b"6 7\n0 1 1\n1 2 10\n2 5 1\n0 3 5\n3 4 1\n4 5 5\n1 4 2\n";
        let queries_bytes = b"0 5\n";
        let out = run_traverse(graph_bytes, queries_bytes).unwrap();
        assert_eq!(out, b"8\n");
    }

    // Pseudo-random number generator for deterministic randomized differential testing
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
        // Runs 50 randomized directed graphs comparing sequential vs bidirectional Dijkstra
        let mut rng = SimpleRng::new(0xDEADBEEFCAFE);

        for _ in 0..50 {
            let n = rng.gen_range(5, 30);
            let m = rng.gen_range(5, 80);

            let mut graph_str = format!("{} {}\n", n, m);
            for _ in 0..m {
                let u = rng.gen_range(0, n - 1);
                let v = rng.gen_range(0, n - 1);
                // Allow weights including 0 and up to 1000
                let w = if rng.gen_range(0, 10) == 0 {
                    0
                } else {
                    rng.gen_range(1, 1000)
                };
                graph_str.push_str(&format!("{} {} {}\n", u, v, w));
            }

            let graph = parse_graph(graph_str.as_bytes()).unwrap();
            let mut ctx = DijkstraContext::new(graph.num_nodes);

            // Test every pair of nodes in this graph
            for s in 0..n {
                for t in 0..n {
                    let seq_ans = ctx.sequential_shortest_path(&graph, s, t);
                    let bidi_ans = ctx.bidirectional_shortest_path(&graph, s, t);

                    assert_eq!(
                        seq_ans, bidi_ans,
                        "Mismatch on query ({} -> {}) in graph with n={}, m={}: seq={}, bidi={}",
                        s, t, n, m, seq_ans, bidi_ans
                    );

                    // Verify that WCC never rejects a reachable pair
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
}
