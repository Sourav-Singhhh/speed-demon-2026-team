use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

#[inline(always)]
pub fn hash_bytes(mut b: &[u8]) -> u64 {
    const K: u64 = 0x517cc1b727220a95;
    let mut h = 0u64;
    while b.len() >= 8 {
        h = (h.rotate_left(5) ^ u64::from_ne_bytes(b[..8].try_into().unwrap())).wrapping_mul(K);
        b = &b[8..];
    }
    if b.len() >= 4 {
        h = (h.rotate_left(5) ^ (u32::from_ne_bytes(b[..4].try_into().unwrap()) as u64)).wrapping_mul(K);
        b = &b[4..];
    }
    for &x in b { h = (h.rotate_left(5) ^ (x as u64)).wrapping_mul(K); }
    h
}

#[derive(Default)]
pub struct FxHasher(u64);
impl std::hash::Hasher for FxHasher {
    #[inline(always)]
    fn finish(&self) -> u64 { self.0 }
    #[inline(always)]
    fn write(&mut self, b: &[u8]) { self.0 = hash_bytes(b); }
}
pub type FastBuildHasher = std::hash::BuildHasherDefault<FxHasher>;
pub type FastHashMap<K, V> = HashMap<K, V, FastBuildHasher>;
pub type FastHashSet<K> = HashSet<K, FastBuildHasher>;

static TOKEN_LUT: [u8; 256] = {
    let mut lut = [0u8; 256];
    let mut i = 0usize;
    while i < 256 {
        let b = i as u8;
        lut[i] = if (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') { b }
        else if b >= b'A' && b <= b'Z' { b + 32 } else { 0 };
        i += 1;
    }
    lut
};

#[inline(always)]
pub fn for_each_token<F: FnMut(&[u8])>(text: &[u8], scratch: &mut Vec<u8>, mut f: F) {
    let mut i = 0;
    while i < text.len() {
        while i < text.len() && TOKEN_LUT[text[i] as usize] == 0 { i += 1; }
        if i >= text.len() { break; }
        let (start, mut has_upper) = (i, false);
        while i < text.len() {
            let c = TOKEN_LUT[text[i] as usize];
            if c == 0 { break; }
            if c != text[i] { has_upper = true; }
            i += 1;
        }
        let raw = &text[start..i];
        if has_upper {
            scratch.clear();
            for &b in raw { scratch.push(TOKEN_LUT[b as usize]); }
            f(scratch);
        } else { f(raw); }
    }
}

#[inline(always)]
pub fn for_each_line<F: FnMut(&[u8])>(chunk: &[u8], mut f: F) {
    let mut pos = 0;
    while pos < chunk.len() {
        let start = pos;
        while pos < chunk.len() && chunk[pos] != b'\n' { pos += 1; }
        let mut end = pos;
        if pos < chunk.len() && chunk[pos] == b'\n' { pos += 1; }
        if end > start && chunk[end - 1] == b'\r' { end -= 1; }
        let line = &chunk[start..end];
        if !line.is_empty() { f(line); }
    }
}

pub const SENTINEL_TOKEN_ID: u16 = 0xFFFF;
const BLOOM_WORDS: usize = 16384;
const BLOOM_MASK: usize = (BLOOM_WORDS * 64) - 1;

pub struct FastBloom(Box<[u64; BLOOM_WORDS]>);
impl FastBloom {
    pub fn new() -> Self { Self(vec![0u64; BLOOM_WORDS].into_boxed_slice().try_into().unwrap()) }
    #[inline(always)]
    pub fn insert(&mut self, h: u64) {
        let (b1, b2, b3) = ((h as usize) & BLOOM_MASK, ((h >> 20) as usize) & BLOOM_MASK, ((h >> 40) as usize) & BLOOM_MASK);
        self.0[b1 / 64] |= 1u64 << (b1 % 64);
        self.0[b2 / 64] |= 1u64 << (b2 % 64);
        self.0[b3 / 64] |= 1u64 << (b3 % 64);
    }
    #[inline(always)]
    pub fn might_contain(&self, h: u64) -> bool {
        let (b1, b2, b3) = ((h as usize) & BLOOM_MASK, ((h >> 20) as usize) & BLOOM_MASK, ((h >> 40) as usize) & BLOOM_MASK);
        ((self.0[b1 / 64] & (1u64 << (b1 % 64))) != 0) && ((self.0[b2 / 64] & (1u64 << (b2 % 64))) != 0) && ((self.0[b3 / 64] & (1u64 << (b3 % 64))) != 0)
    }
}

pub struct QueryVocabularies {
    pub bloom: FastBloom,
    pub all_terms_map: FastHashMap<Vec<u8>, u32>,
    pub phrase_terms_map: FastHashMap<Vec<u8>, u16>,
    pub term_to_phrase_id: Vec<u16>,
}

impl QueryVocabularies {
    pub fn extract(queries_data: &[u8]) -> Self {
        let (mut all_set, mut phrase_set) = (FastHashSet::default(), FastHashSet::default());
        for_each_line(queries_data, |line| {
            if line.starts_with(b"BOOL ") {
                for p in line[5..].split(|&b| b == b' ') {
                    if p != b"AND" && p != b"OR" && p != b"NOT" && !p.is_empty() { all_set.insert(p.to_vec()); }
                }
            } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") && line.len() >= 9 {
                for t in line[8..line.len() - 1].split(|&b| b == b' ') {
                    if !t.is_empty() { all_set.insert(t.to_vec()); phrase_set.insert(t.to_vec()); }
                }
            }
        });
        let mut sorted_all: Vec<Vec<u8>> = all_set.into_iter().collect();
        sorted_all.sort_unstable();
        let mut sorted_phrase: Vec<Vec<u8>> = phrase_set.into_iter().collect();
        sorted_phrase.sort_unstable();

        let mut phrase_terms_map = FastHashMap::with_capacity_and_hasher(sorted_phrase.len(), FastBuildHasher::default());
        for (id, tok) in sorted_phrase.into_iter().enumerate() { phrase_terms_map.insert(tok, id as u16); }

        let mut all_terms_map = FastHashMap::with_capacity_and_hasher(sorted_all.len(), FastBuildHasher::default());
        let mut term_to_phrase_id = Vec::with_capacity(sorted_all.len());
        let mut bloom = FastBloom::new();

        for (id, tok) in sorted_all.into_iter().enumerate() {
            let pid = phrase_terms_map.get(&tok).copied().unwrap_or(SENTINEL_TOKEN_ID);
            bloom.insert(hash_bytes(&tok));
            all_terms_map.insert(tok, id as u32);
            term_to_phrase_id.push(pid);
        }
        Self { bloom, all_terms_map, phrase_terms_map, term_to_phrase_id }
    }

    #[inline(always)]
    pub fn get_term_id(&self, tok: &[u8]) -> Option<u32> {
        let h = hash_bytes(tok);
        if !self.bloom.might_contain(h) { return None; }
        self.all_terms_map.get(tok).copied()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BoolOp { And, Or, Not }

pub enum ParsedQuery {
    Bool { first_term: Vec<u8>, clauses: Vec<(BoolOp, Vec<u8>)> },
    Phrase { terms: Vec<Vec<u8>> },
    Empty,
}

pub fn parse_all_queries(queries_data: &[u8]) -> Vec<ParsedQuery> {
    let mut queries = Vec::new();
    for_each_line(queries_data, |line| {
        if line.starts_with(b"BOOL ") {
            let mut parts = line[5..].split(|&b| b == b' ');
            let first = match parts.next() { Some(t) if !t.is_empty() => t.to_vec(), _ => { queries.push(ParsedQuery::Empty); return; } };
            let mut clauses = Vec::new();
            while let Some(op_b) = parts.next() {
                let op = match op_b { b"AND" => BoolOp::And, b"OR" => BoolOp::Or, b"NOT" => BoolOp::Not, _ => continue };
                if let Some(t) = parts.next() { if !t.is_empty() { clauses.push((op, t.to_vec())); } }
            }
            queries.push(ParsedQuery::Bool { first_term: first, clauses });
        } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") && line.len() >= 9 {
            let terms: Vec<Vec<u8>> = line[8..line.len() - 1].split(|&b| b == b' ').filter(|t| !t.is_empty()).map(|t| t.to_vec()).collect();
            queries.push(if terms.is_empty() { ParsedQuery::Empty } else { ParsedQuery::Phrase { terms } });
        } else { queries.push(ParsedQuery::Empty); }
    });
    queries
}

#[derive(Clone, Copy, Default)]
pub struct TrieNode { edges_start: u32, edges_len: u16, match_start: u32, match_len: u16 }
#[derive(Clone, Copy)]
pub struct TrieEdge { pid: u16, next_node: u32 }

pub struct PhraseTrie {
    pub root_transitions: Vec<u32>,
    pub nodes: Vec<TrieNode>,
    pub edges: Vec<TrieEdge>,
    pub matches: Vec<u32>,
}

impl PhraseTrie {
    pub fn build(vocab: &QueryVocabularies, queries: &[ParsedQuery]) -> Self {
        let (mut temp_edges, mut temp_matches) = (vec![FastHashMap::<u16, u32>::default()], vec![Vec::<u32>::new()]);
        for (q_idx, query) in queries.iter().enumerate() {
            if let ParsedQuery::Phrase { terms } = query {
                let mut pids = Vec::with_capacity(terms.len());
                let mut valid = true;
                for t in terms {
                    if let Some(&pid) = vocab.phrase_terms_map.get(t) { pids.push(pid); } else { valid = false; break; }
                }
                if !valid || pids.is_empty() { continue; }
                let mut curr = 0usize;
                for &pid in &pids {
                    curr = match temp_edges[curr].get(&pid) {
                        Some(&nxt) => nxt as usize,
                        None => {
                            let nxt = temp_edges.len();
                            temp_edges.push(FastHashMap::default());
                            temp_matches.push(Vec::new());
                            temp_edges[curr].insert(pid, nxt as u32);
                            nxt
                        }
                    };
                }
                temp_matches[curr].push(q_idx as u32);
            }
        }
        let num_phrase_terms = vocab.phrase_terms_map.len();
        let mut root_transitions = vec![0u32; num_phrase_terms];
        for (&pid, &nxt) in &temp_edges[0] {
            if (pid as usize) < num_phrase_terms { root_transitions[pid as usize] = nxt; }
        }
        let (mut nodes, mut edges, mut matches) = (Vec::with_capacity(temp_edges.len()), Vec::new(), Vec::new());
        for i in 0..temp_edges.len() {
            let edges_start = edges.len() as u32;
            let mut ne: Vec<TrieEdge> = temp_edges[i].iter().map(|(&pid, &next_node)| TrieEdge { pid, next_node }).collect();
            ne.sort_unstable_by_key(|e| e.pid);
            let edges_len = ne.len() as u16;
            edges.extend_from_slice(&ne);

            let match_start = matches.len() as u32;
            let match_len = temp_matches[i].len() as u16;
            matches.extend_from_slice(&temp_matches[i]);
            nodes.push(TrieNode { edges_start, edges_len, match_start, match_len });
        }
        Self { root_transitions, nodes, edges, matches }
    }

    #[inline(always)]
    pub fn transition(&self, node_idx: u32, pid: u16) -> u32 {
        let node = unsafe { self.nodes.get_unchecked(node_idx as usize) };
        let slice = unsafe { self.edges.get_unchecked(node.edges_start as usize..node.edges_start as usize + node.edges_len as usize) };
        if node.edges_len == 1 { return if slice[0].pid == pid { slice[0].next_node } else { 0 }; }
        slice.binary_search_by_key(&pid, |e| e.pid).map(|i| slice[i].next_node).unwrap_or(0)
    }

    #[inline(always)]
    pub fn record_matches(&self, node_idx: u32, doc_id: u32, last_doc: &mut [u32], matches: &mut Vec<(u32, u32)>) {
        let n = unsafe { self.nodes.get_unchecked(node_idx as usize) };
        for &q in unsafe { self.matches.get_unchecked(n.match_start as usize..n.match_start as usize + n.match_len as usize) } {
            if unsafe { *last_doc.get_unchecked(q as usize) != doc_id } {
                unsafe { *last_doc.get_unchecked_mut(q as usize) = doc_id; }
                matches.push((q, doc_id));
            }
        }
    }

    #[inline(always)]
    pub fn advance(&self, pid: u16, doc_id: u32, active: &mut [u32; 16], active_len: &mut usize, last_doc: &mut [u32], matches: &mut Vec<(u32, u32)>) {
        let (mut next_active, mut next_len) = ([0u32; 16], 0);
        for i in 0..*active_len {
            let nxt = self.transition(active[i], pid);
            if nxt != 0 {
                if next_len < 16 { next_active[next_len] = nxt; next_len += 1; }
                self.record_matches(nxt, doc_id, last_doc, matches);
            }
        }
        let root_nxt = if (pid as usize) < self.root_transitions.len() { unsafe { *self.root_transitions.get_unchecked(pid as usize) } } else { 0 };
        if root_nxt != 0 {
            if next_len < 16 { next_active[next_len] = root_nxt; next_len += 1; }
            self.record_matches(root_nxt, doc_id, last_doc, matches);
        }
        *active = next_active;
        *active_len = next_len;
    }
}

pub enum PostingRef<'a> {
    Sparse(&'a [u32]),
    Dense(&'a [u64]),
}

pub struct CorpusIndex {
    pub num_docs: usize,
    pub postings_offsets: Vec<u32>,
    pub postings_data: Vec<u32>,
    pub dense_bitsets: Vec<u64>,
    pub dense_term_map: Vec<Option<u32>>,
    pub words_per_bitset: usize,
    pub vocab: QueryVocabularies,
    pub phrase_postings: Vec<Vec<u32>>,
}

impl CorpusIndex {
    #[inline(always)]
    pub fn get_postings(&self, term_id: u32) -> Option<PostingRef<'_>> {
        let id = term_id as usize;
        if id < self.dense_term_map.len() {
            if let Some(d_idx) = self.dense_term_map[id] {
                let start = d_idx as usize * self.words_per_bitset;
                return Some(PostingRef::Dense(&self.dense_bitsets[start..start + self.words_per_bitset]));
            }
        }
        if id + 1 < self.postings_offsets.len() {
            let (start, end) = (self.postings_offsets[id] as usize, self.postings_offsets[id + 1] as usize);
            if start < end { Some(PostingRef::Sparse(&self.postings_data[start..end])) } else { None }
        } else { None }
    }

    #[inline(always)]
    pub fn get_posting_len(&self, term_id: u32) -> usize {
        let id = term_id as usize;
        if id + 1 < self.postings_offsets.len() { (self.postings_offsets[id + 1] - self.postings_offsets[id]) as usize } else { 0 }
    }

    pub fn build(docs_data: &[u8], vocab: QueryVocabularies, queries: &[ParsedQuery], num_threads: usize) -> Result<Self, String> {
        let actual_workers = num_threads.max(1);
        let chunks = partition_docs_data(docs_data, actual_workers);
        let num_terms = vocab.all_terms_map.len();

        let pass1_results = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(chunks.len());
            for chunk in &chunks {
                let v = &vocab;
                handles.push(s.spawn(move || {
                    let mut term_counts = vec![0u32; num_terms];
                    let mut seen_epoch = vec![0u32; num_terms];
                    let mut current_epoch = 1u32;
                    let mut scratch = Vec::with_capacity(32);
                    let (mut first_doc_id, mut num_docs, mut has_first) = (0, 0, false);
                    for_each_line(chunk, |line| {
                        let tab_pos = match line.iter().position(|&b| b == b'\t') { Some(p) => p, None => return };
                        let mut doc_id = 0usize;
                        for &b in &line[..tab_pos] { doc_id = doc_id * 10 + (b.wrapping_sub(b'0')) as usize; }
                        if !has_first { first_doc_id = doc_id; has_first = true; }
                        current_epoch += 1;
                        if current_epoch == u32::MAX { seen_epoch.fill(0); current_epoch = 1; }
                        for_each_token(&line[tab_pos + 1..], &mut scratch, |tok| {
                            if let Some(tid) = v.get_term_id(tok) {
                                let idx = tid as usize;
                                if seen_epoch[idx] != current_epoch { seen_epoch[idx] = current_epoch; term_counts[idx] += 1; }
                            }
                        });
                        num_docs += 1;
                    });
                    (first_doc_id, num_docs, term_counts)
                }));
            }
            let mut res = Vec::new();
            for h in handles { res.push(h.join().unwrap()); }
            res
        });

        let mut total_docs = 0;
        let mut total_term_counts = vec![0u32; num_terms];
        for (_, num_docs, term_counts) in &pass1_results {
            total_docs += num_docs;
            for (i, &cnt) in term_counts.iter().enumerate() { total_term_counts[i] += cnt; }
        }

        let mut postings_offsets = Vec::with_capacity(num_terms + 1);
        postings_offsets.push(0);
        let mut total_postings = 0u32;
        for &cnt in &total_term_counts { total_postings += cnt; postings_offsets.push(total_postings); }

        let mut worker_ptrs: Vec<Vec<u32>> = Vec::with_capacity(pass1_results.len());
        let mut running_worker_starts = vec![0u32; num_terms];
        for (_, _, term_counts) in &pass1_results {
            let mut ptrs = Vec::with_capacity(num_terms);
            for t in 0..num_terms {
                ptrs.push(postings_offsets[t] + running_worker_starts[t]);
                running_worker_starts[t] += term_counts[t];
            }
            worker_ptrs.push(ptrs);
        }

        let mut postings_data = vec![0u32; total_postings as usize];
        let phrase_trie = PhraseTrie::build(&vocab, queries);

        let thread_matches = std::thread::scope(|s| {
            let postings_ptr = postings_data.as_mut_ptr() as usize;
            let mut handles = Vec::with_capacity(chunks.len());
            for (w_idx, chunk) in chunks.iter().enumerate() {
                let (v, trie, mut ptrs, num_q) = (&vocab, &phrase_trie, std::mem::take(&mut worker_ptrs[w_idx]), queries.len());
                handles.push(s.spawn(move || {
                    let raw = postings_ptr as *mut u32;
                    let (mut seen_in_doc, mut scratch, mut last_doc, mut local_matches) = (Vec::with_capacity(256), Vec::with_capacity(32), vec![u32::MAX; num_q], Vec::with_capacity(2048));
                    for_each_line(chunk, |line| {
                        let tab_pos = match line.iter().position(|&b| b == b'\t') { Some(p) => p, None => return };
                        let mut doc_id = 0u32;
                        for &b in &line[..tab_pos] { doc_id = doc_id * 10 + (b.wrapping_sub(b'0')) as u32; }
                        seen_in_doc.clear();
                        let (mut active, mut active_len) = ([0u32; 16], 0);

                        for_each_token(&line[tab_pos + 1..], &mut scratch, |tok| {
                            if let Some(tid) = v.get_term_id(tok) {
                                seen_in_doc.push(tid);
                                let pid = unsafe { *v.term_to_phrase_id.get_unchecked(tid as usize) };
                                if pid != SENTINEL_TOKEN_ID {
                                    trie.advance(pid, doc_id, &mut active, &mut active_len, &mut last_doc, &mut local_matches);
                                } else { active_len = 0; }
                            } else { active_len = 0; }
                        });
                        seen_in_doc.sort_unstable();
                        seen_in_doc.dedup();
                        for &tid in &seen_in_doc {
                            let out_pos = ptrs[tid as usize] as usize;
                            unsafe { *raw.add(out_pos) = doc_id; }
                            ptrs[tid as usize] += 1;
                        }
                    });
                    local_matches
                }));
            }
            let mut res = Vec::new();
            for h in handles { res.push(h.join().unwrap()); }
            res
        });

        let mut phrase_postings: Vec<Vec<u32>> = vec![Vec::new(); queries.len()];
        for w_matches in thread_matches {
            for (q_idx, doc_id) in w_matches { phrase_postings[q_idx as usize].push(doc_id); }
        }

        let dense_threshold = (total_docs / 32).max(64);
        let mut dense_term_map = vec![None; num_terms];
        let mut num_dense = 0;
        for (tid, &count) in total_term_counts.iter().enumerate() {
            if count as usize >= dense_threshold { dense_term_map[tid] = Some(num_dense as u32); num_dense += 1; }
        }
        let words_per_bitset = (total_docs + 63) / 64;
        let mut dense_bitsets = vec![0u64; num_dense * words_per_bitset];
        for (tid, &dense_idx_opt) in dense_term_map.iter().enumerate() {
            if let Some(d_idx) = dense_idx_opt {
                let start_word = d_idx as usize * words_per_bitset;
                for &doc_id in &postings_data[postings_offsets[tid] as usize..postings_offsets[tid + 1] as usize] {
                    let id = doc_id as usize;
                    if id < total_docs { dense_bitsets[start_word + (id / 64)] |= 1u64 << (id % 64); }
                }
            }
        }
        Ok(Self { num_docs: total_docs, postings_offsets, postings_data, dense_bitsets, dense_term_map, words_per_bitset, vocab, phrase_postings })
    }
}

pub fn partition_docs_data(d: &[u8], n: usize) -> Vec<&[u8]> {
    if d.is_empty() || n <= 1 { return vec![d]; }
    let mut bounds = vec![0];
    for i in 1..n {
        let mut b = (i * d.len()) / n;
        while b < d.len() && d[b] != b'\n' { b += 1; }
        bounds.push((b + 1).min(d.len()));
    }
    bounds.push(d.len());
    bounds.dedup();
    (0..bounds.len() - 1).map(|i| &d[bounds[i]..bounds[i + 1]]).collect()
}

pub struct BitSet(pub Vec<u64>);
impl BitSet {
    pub fn new(num_bits: usize) -> Self { Self(vec![0u64; (num_bits + 63) / 64]) }
    #[inline(always)]
    pub fn clear(&mut self) { self.0.fill(0); }
    #[inline(always)]
    pub fn load_dense(&mut self, dense: &[u64]) {
        let n = self.0.len().min(dense.len());
        self.0[..n].copy_from_slice(&dense[..n]);
    }
    #[inline(always)]
    pub fn load_sparse(&mut self, docs: &[u32]) { self.clear(); self.apply_sparse(BoolOp::Or, docs); }
    #[inline(always)]
    pub fn apply_sparse(&mut self, op: BoolOp, docs: &[u32]) {
        if op == BoolOp::And {
            let mut new_w = vec![0u64; self.0.len()];
            for &d in docs {
                let (w, bit) = (d as usize / 64, 1u64 << (d % 64));
                if w < self.0.len() && (self.0[w] & bit) != 0 { new_w[w] |= bit; }
            }
            self.0 = new_w;
        } else {
            for &d in docs {
                let (w, bit) = (d as usize / 64, 1u64 << (d % 64));
                if w < self.0.len() {
                    if op == BoolOp::Or { self.0[w] |= bit; } else { self.0[w] &= !bit; }
                }
            }
        }
    }
    #[inline(always)]
    pub fn apply_dense(&mut self, op: BoolOp, dense: &[u64]) {
        let n = self.0.len().min(dense.len());
        match op {
            BoolOp::And => for i in 0..n { self.0[i] &= dense[i]; },
            BoolOp::Or => for i in 0..n { self.0[i] |= dense[i]; },
            BoolOp::Not => for i in 0..n { self.0[i] &= !dense[i]; },
        }
    }
    #[inline(always)]
    pub fn apply(&mut self, op: BoolOp, post: Option<PostingRef<'_>>) {
        match post {
            Some(PostingRef::Sparse(s)) => self.apply_sparse(op, s),
            Some(PostingRef::Dense(d)) => self.apply_dense(op, d),
            None => if op == BoolOp::And { self.clear(); },
        }
    }
    pub fn summary(&self) -> (usize, u64, Vec<u32>) {
        let (mut count, mut sum, mut first_10) = (0usize, 0u64, Vec::with_capacity(10));
        for (w_idx, &word) in self.0.iter().enumerate() {
            if word != 0 {
                count += word.count_ones() as usize;
                let (mut bits, base) = (word, (w_idx * 64) as u64);
                while bits != 0 {
                    let id = base + bits.trailing_zeros() as u64;
                    sum += id;
                    if first_10.len() < 10 { first_10.push(id as u32); }
                    bits &= bits - 1;
                }
            }
        }
        (count, sum, first_10)
    }
}

#[inline(always)]
fn write_res(count: usize, sum: u64, ids: &[u32], out: &mut String) {
    if count == 0 { out.push_str("0 0\n"); return; }
    use std::fmt::Write;
    let _ = write!(out, "{} {}", count, sum);
    for &id in &ids[..count.min(10)] { let _ = write!(out, " {}", id); }
    out.push('\n');
}

pub struct QueryEvaluator {
    pub bitset: BitSet,
    pub candidate_docs: Vec<u32>,
    pub sorted_and_terms: Vec<(usize, u32)>,
}

impl QueryEvaluator {
    pub fn new(num_docs: usize) -> Self {
        Self { bitset: BitSet::new(num_docs), candidate_docs: Vec::with_capacity(1024), sorted_and_terms: Vec::with_capacity(8) }
    }

    pub fn evaluate_parsed_query(&mut self, query_idx: usize, query: &ParsedQuery, corpus: &CorpusIndex, output: &mut String) {
        match query {
            ParsedQuery::Bool { first_term, clauses } => {
                if clauses.iter().all(|(op, _)| *op == BoolOp::And) {
                    self.sorted_and_terms.clear();
                    for t in std::iter::once(first_term).chain(clauses.iter().map(|(_, t)| t)) {
                        let tid = match corpus.vocab.get_term_id(t) { Some(id) => id, None => { output.push_str("0 0\n"); return; } };
                        let len = corpus.get_posting_len(tid);
                        if len == 0 { output.push_str("0 0\n"); return; }
                        self.sorted_and_terms.push((len, tid));
                    }
                    self.sorted_and_terms.sort_unstable_by_key(|&(len, _)| len);
                    let (_, rarest_tid) = self.sorted_and_terms[0];
                    match corpus.get_postings(rarest_tid) {
                        Some(PostingRef::Sparse(initial)) => {
                            self.candidate_docs.clear();
                            self.candidate_docs.extend_from_slice(initial);
                            for &(_, tid) in &self.sorted_and_terms[1..] {
                                if self.candidate_docs.is_empty() { break; }
                                match corpus.get_postings(tid) {
                                    Some(PostingRef::Sparse(other)) => self.candidate_docs.retain(|&id| other.binary_search(&id).is_ok()),
                                    Some(PostingRef::Dense(words)) => self.candidate_docs.retain(|&id| {
                                        let idx = id as usize;
                                        (words[idx / 64] & (1u64 << (idx % 64))) != 0
                                    }),
                                    None => { self.candidate_docs.clear(); break; }
                                }
                            }
                            let count = self.candidate_docs.len();
                            let sum: u64 = self.candidate_docs.iter().map(|&id| id as u64).sum();
                            write_res(count, sum, &self.candidate_docs, output);
                            return;
                        }
                        Some(PostingRef::Dense(words)) => {
                            self.bitset.load_dense(words);
                            for &(_, tid) in &self.sorted_and_terms[1..] { self.bitset.apply(BoolOp::And, corpus.get_postings(tid)); }
                            let (count, sum, first_10) = self.bitset.summary();
                            write_res(count, sum, &first_10, output);
                            return;
                        }
                        None => { output.push_str("0 0\n"); return; }
                    }
                }
                match corpus.vocab.get_term_id(first_term).and_then(|id| corpus.get_postings(id)) {
                    Some(PostingRef::Sparse(s)) => self.bitset.load_sparse(s),
                    Some(PostingRef::Dense(d)) => self.bitset.load_dense(d),
                    None => self.bitset.clear(),
                }
                for (op, term) in clauses {
                    let post = corpus.vocab.get_term_id(term).and_then(|id| corpus.get_postings(id));
                    self.bitset.apply(*op, post);
                }
                let (count, sum, first_10) = self.bitset.summary();
                write_res(count, sum, &first_10, output);
            }
            ParsedQuery::Phrase { .. } => {
                let docs = &corpus.phrase_postings[query_idx];
                let sum: u64 = docs.iter().map(|&id| id as u64).sum();
                write_res(docs.len(), sum, docs, output);
            }
            ParsedQuery::Empty => output.push_str("0 0\n"),
        }
    }
}

pub fn parallel_evaluate_queries(corpus: &CorpusIndex, queries: &[ParsedQuery], num_threads: usize) -> Vec<String> {
    if queries.is_empty() { return Vec::new(); }
    let actual_threads = num_threads.max(1).min(queries.len());
    let next_query_idx = AtomicUsize::new(0);

    let thread_results: Vec<Vec<(usize, String)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(actual_threads);
        for _ in 0..actual_threads {
            let next = &next_query_idx;
            handles.push(s.spawn(move || {
                let (mut evaluator, mut local_results, mut buf) = (QueryEvaluator::new(corpus.num_docs), Vec::with_capacity(queries.len() / actual_threads + 32), String::with_capacity(64));
                loop {
                    let idx = next.fetch_add(1, Ordering::Relaxed);
                    if idx >= queries.len() { break; }
                    buf.clear();
                    evaluator.evaluate_parsed_query(idx, &queries[idx], corpus, &mut buf);
                    local_results.push((idx, buf.clone()));
                }
                local_results
            }));
        }
        let mut res = Vec::new();
        for h in handles { res.push(h.join().unwrap()); }
        res
    });

    let mut answers = vec![String::new(); queries.len()];
    for local_res in thread_results {
        for (idx, ans) in local_res { answers[idx] = ans; }
    }
    answers
}

#[cfg(target_os = "linux")]
fn mmap_file(file: &fs::File, len: usize) -> Result<&'static [u8], String> {
    use std::os::unix::io::AsRawFd;
    let (fd, addr): (i32, *mut u8);
    fd = file.as_raw_fd();
    unsafe {
        std::arch::asm!(
            "syscall",
            in("rax") 9usize, in("rdi") 0usize, in("rsi") len, in("rdx") 1usize, in("r10") 2usize, in("r8") fd, in("r9") 0usize,
            lateout("rax") addr, lateout("rcx") _, lateout("r11") _,
        );
    }
    if (addr as isize) < 0 && (addr as isize) > -4096 { return Err(format!("mmap error {}", -(addr as isize))); }
    unsafe { Ok(std::slice::from_raw_parts(addr, len)) }
}
#[cfg(not(target_os = "linux"))]
fn mmap_file(_f: &fs::File, _len: usize) -> Result<&'static [u8], String> { Err("linux only".into()) }

fn munmap_file(data: &[u8]) {
    #[cfg(target_os = "linux")]
    unsafe {
        std::arch::asm!("syscall", in("rax") 11usize, in("rdi") data.as_ptr() as usize, in("rsi") data.len(), lateout("rax") _, lateout("rcx") _, lateout("r11") _);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let (data_dir, out_dir) = (if args.len() > 1 { &args[1] } else { "/data" }, if args.len() > 2 { &args[2] } else { "/out" });
    let queries_data = fs::read(Path::new(data_dir).join("queries.txt")).expect("read queries.txt");
    let num_threads = env::var("NUM_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let (vocab, parsed_queries) = (QueryVocabularies::extract(&queries_data), parse_all_queries(&queries_data));
    drop(queries_data);

    let docs_file = fs::File::open(Path::new(data_dir).join("docs.txt")).expect("open docs.txt");
    let docs_len = docs_file.metadata().expect("docs metadata").len() as usize;

    let (corpus, docs_data) = if docs_len > 0 {
        let data = mmap_file(&docs_file, docs_len).expect("mmap failed");
        (CorpusIndex::build(data, vocab, &parsed_queries, num_threads).expect("build failed"), Some(data))
    } else {
        (CorpusIndex::build(&[], vocab, &parsed_queries, num_threads).expect("build failed"), None)
    };
    if let Some(d) = docs_data { munmap_file(d); }
    drop(docs_file);

    let results = parallel_evaluate_queries(&corpus, &parsed_queries, num_threads);
    let mut out = String::with_capacity(parsed_queries.len() * 32);
    for r in &results { out.push_str(r); }
    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("create out dir");
    fs::write(out_dir_path.join("results.txt"), out.into_bytes()).expect("write results");
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_queries() {
        let docs = b"0\tuniversal even\n1\tuniversal odd\n";
        let q = b"BOOL universal\nBOOL missing\nPHRASE \"universal even\"\n";
        let (v, pq) = (QueryVocabularies::extract(q), parse_all_queries(q));
        let c = CorpusIndex::build(docs, v, &pq, 2).unwrap();
        let res = parallel_evaluate_queries(&c, &pq, 2);
        assert_eq!(res[0], "2 1 0 1\n");
        assert_eq!(res[1], "0 0\n");
        assert_eq!(res[2], "1 0 0\n");
    }
}

