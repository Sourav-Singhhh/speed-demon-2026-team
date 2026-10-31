use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

#[inline]
pub fn is_token_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric()
}

pub fn for_each_token<F>(text: &[u8], scratch: &mut Vec<u8>, mut on_token: F)
where
    F: FnMut(&[u8]),
{
    let mut i = 0;
    while i < text.len() {
        while i < text.len() && !is_token_byte(text[i]) {
            i += 1;
        }
        if i >= text.len() {
            break;
        }
        let start = i;
        let mut has_upper = false;
        while i < text.len() && is_token_byte(text[i]) {
            if text[i].is_ascii_uppercase() {
                has_upper = true;
            }
            i += 1;
        }
        let raw = &text[start..i];
        if has_upper {
            scratch.clear();
            scratch.extend(raw.iter().map(|b| b.to_ascii_lowercase()));
            on_token(scratch);
        } else {
            on_token(raw);
        }
    }
}

pub fn tokenize(text: &[u8]) -> Vec<Vec<u8>> {
    let mut tokens = Vec::new();
    let mut scratch = Vec::with_capacity(32);
    for_each_token(text, &mut scratch, |tok| {
        tokens.push(tok.to_vec());
    });
    tokens
}

pub const SENTINEL_TOKEN_ID: u16 = 0xFFFF;

pub struct QueryVocabularies {
    pub all_terms_map: HashMap<Vec<u8>, u32>,
    pub phrase_terms_map: HashMap<Vec<u8>, u16>,
    pub term_to_phrase_id: Vec<u16>,
}

impl QueryVocabularies {
    pub fn extract(queries_data: &[u8]) -> Self {
        let mut all_set = HashSet::new();
        let mut phrase_set = HashSet::new();

        for line in queries_data.split(|&b| b == b'\n') {
            let line = if line.ends_with(b"\r") {
                &line[..line.len() - 1]
            } else {
                line
            };
            if line.is_empty() {
                continue;
            }
            if line.starts_with(b"BOOL ") {
                let rest = &line[5..];
                for part in rest.split(|&b| b == b' ') {
                    if part != b"AND" && part != b"OR" && part != b"NOT" && !part.is_empty() {
                        all_set.insert(part.to_vec());
                    }
                }
            } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") && line.len() >= 9 {
                let inner = &line[8..line.len() - 1];
                for term in inner.split(|&b| b == b' ') {
                    if !term.is_empty() {
                        all_set.insert(term.to_vec());
                        phrase_set.insert(term.to_vec());
                    }
                }
            }
        }

        let mut sorted_all: Vec<Vec<u8>> = all_set.into_iter().collect();
        sorted_all.sort_unstable();

        let mut sorted_phrase: Vec<Vec<u8>> = phrase_set.into_iter().collect();
        sorted_phrase.sort_unstable();
        assert!(
            sorted_phrase.len() < SENTINEL_TOKEN_ID as usize,
            "Phrase vocabulary exceeds u16 limit!"
        );

        let mut phrase_terms_map = HashMap::with_capacity(sorted_phrase.len());
        for (id, tok) in sorted_phrase.into_iter().enumerate() {
            phrase_terms_map.insert(tok, id as u16);
        }

        let mut all_terms_map = HashMap::with_capacity(sorted_all.len());
        let mut term_to_phrase_id = Vec::with_capacity(sorted_all.len());

        for (id, tok) in sorted_all.into_iter().enumerate() {
            let pid = phrase_terms_map
                .get(&tok)
                .copied()
                .unwrap_or(SENTINEL_TOKEN_ID);
            all_terms_map.insert(tok, id as u32);
            term_to_phrase_id.push(pid);
        }

        Self {
            all_terms_map,
            phrase_terms_map,
            term_to_phrase_id,
        }
    }

    #[inline]
    pub fn get_term_id(&self, tok: &[u8]) -> Option<u32> {
        self.all_terms_map.get(tok).copied()
    }

    #[inline]
    pub fn get_phrase_id(&self, tok: &[u8]) -> Option<u16> {
        self.phrase_terms_map.get(tok).copied()
    }

    #[inline]
    pub fn num_terms(&self) -> usize {
        self.all_terms_map.len()
    }
}

pub enum PostingRef<'a> {
    Sparse(&'a [u32]),
    Dense(&'a [u64]),
}

pub struct CorpusIndex {
    pub num_docs: usize,
    pub total_tokens: usize,
    pub doc_offsets: Vec<u32>,
    pub doc_tokens: Vec<u16>,
    pub postings_offsets: Vec<u32>,
    pub postings_data: Vec<u32>,
    pub dense_bitsets: Vec<u64>,
    pub dense_term_map: Vec<Option<u32>>,
    pub words_per_bitset: usize,
    pub vocab: QueryVocabularies,
}

impl CorpusIndex {
    #[inline]
    pub fn get_postings(&self, term_id: u32) -> Option<PostingRef<'_>> {
        let id = term_id as usize;
        if id < self.dense_term_map.len() {
            if let Some(dense_idx) = self.dense_term_map[id] {
                let start = dense_idx as usize * self.words_per_bitset;
                let end = start + self.words_per_bitset;
                return Some(PostingRef::Dense(&self.dense_bitsets[start..end]));
            }
        }
        if id + 1 < self.postings_offsets.len() {
            let start = self.postings_offsets[id] as usize;
            let end = self.postings_offsets[id + 1] as usize;
            if start < end {
                Some(PostingRef::Sparse(&self.postings_data[start..end]))
            } else {
                None
            }
        } else {
            None
        }
    }

    #[inline]
    pub fn get_sparse_postings(&self, term_id: u32) -> Option<&[u32]> {
        let id = term_id as usize;
        if id + 1 < self.postings_offsets.len() {
            let start = self.postings_offsets[id] as usize;
            let end = self.postings_offsets[id + 1] as usize;
            if start < end {
                Some(&self.postings_data[start..end])
            } else {
                None
            }
        } else {
            None
        }
    }

    #[inline]
    pub fn get_posting_len(&self, term_id: u32) -> usize {
        let id = term_id as usize;
        if id + 1 < self.postings_offsets.len() {
            (self.postings_offsets[id + 1] - self.postings_offsets[id]) as usize
        } else {
            0
        }
    }

    pub fn retained_postings_count(&self) -> usize {
        self.postings_data.len()
    }

    pub fn build(docs_data: &[u8], vocab: QueryVocabularies, num_threads: usize) -> Result<Self, String> {
        let actual_workers = num_threads.max(1);
        let chunks = partition_docs_data(docs_data, actual_workers);
        let num_terms = vocab.num_terms();

        struct Pass1Result {
            first_doc_id: usize,
            num_docs: usize,
            total_tokens: usize,
            term_counts: Vec<u32>,
        }

        let pass1_results: Result<Vec<Pass1Result>, String> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(chunks.len());
            for chunk in &chunks {
                let vocab_ref = &vocab;
                handles.push(s.spawn(move || {
                    let mut term_counts = vec![0u32; num_terms];
                    let mut seen_epoch = vec![0u32; num_terms];
                    let mut current_epoch = 1u32;
                    let mut scratch = Vec::with_capacity(32);

                    let mut pos = 0;
                    let mut first_doc_id = 0;
                    let mut num_docs = 0;
                    let mut total_tokens = 0;
                    let mut has_first = false;

                    while pos < chunk.len() {
                        let line_start = pos;
                        while pos < chunk.len() && chunk[pos] != b'\n' {
                            pos += 1;
                        }
                        let mut line_end = pos;
                        if pos < chunk.len() && chunk[pos] == b'\n' {
                            pos += 1;
                        }
                        if line_end > line_start && chunk[line_end - 1] == b'\r' {
                            line_end -= 1;
                        }
                        let line = &chunk[line_start..line_end];
                        if line.is_empty() {
                            continue;
                        }

                        let tab_pos = line
                            .iter()
                            .position(|&b| b == b'\t')
                            .ok_or_else(|| "missing TAB in doc line".to_string())?;

                        let id_bytes = &line[..tab_pos];
                        let id_str = std::str::from_utf8(id_bytes).map_err(|e| e.to_string())?;
                        let doc_id: usize =
                            id_str.parse().map_err(|e: std::num::ParseIntError| e.to_string())?;

                        if !has_first {
                            first_doc_id = doc_id;
                            has_first = true;
                        } else {
                            let expected = first_doc_id + num_docs;
                            if doc_id != expected {
                                return Err(format!("expected doc id {}, got {}", expected, doc_id));
                            }
                        }

                        let text = &line[tab_pos + 1..];
                        current_epoch += 1;
                        if current_epoch == u32::MAX {
                            seen_epoch.fill(0);
                            current_epoch = 1;
                        }

                        for_each_token(text, &mut scratch, |tok| {
                            total_tokens += 1;
                            if let Some(tid) = vocab_ref.get_term_id(tok) {
                                let idx = tid as usize;
                                if seen_epoch[idx] != current_epoch {
                                    seen_epoch[idx] = current_epoch;
                                    term_counts[idx] += 1;
                                }
                            }
                        });

                        num_docs += 1;
                    }

                    Ok(Pass1Result {
                        first_doc_id,
                        num_docs,
                        total_tokens,
                        term_counts,
                    })
                }));
            }

            let mut res = Vec::with_capacity(handles.len());
            for h in handles {
                res.push(h.join().unwrap()?);
            }
            Ok(res)
        });

        let pass1_results = pass1_results?;

        let mut total_docs = 0;
        let mut total_tokens = 0;
        let mut expected_doc = 0;
        let mut worker_doc_starts = Vec::with_capacity(pass1_results.len());
        let mut worker_token_starts = Vec::with_capacity(pass1_results.len());

        for r in &pass1_results {
            worker_doc_starts.push(total_docs);
            worker_token_starts.push(total_tokens);
            if r.num_docs > 0 {
                if r.first_doc_id != expected_doc {
                    return Err(format!("doc gap: expected {}, got {}", expected_doc, r.first_doc_id));
                }
                expected_doc += r.num_docs;
                total_docs += r.num_docs;
                total_tokens += r.total_tokens;
            }
        }

        let mut total_term_counts = vec![0u32; num_terms];
        for r in &pass1_results {
            for (i, &cnt) in r.term_counts.iter().enumerate() {
                total_term_counts[i] += cnt;
            }
        }

        let mut postings_offsets = Vec::with_capacity(num_terms + 1);
        postings_offsets.push(0);
        let mut total_postings = 0u32;
        for &cnt in &total_term_counts {
            total_postings += cnt;
            postings_offsets.push(total_postings);
        }

        let mut worker_ptrs: Vec<Vec<u32>> = Vec::with_capacity(pass1_results.len());
        let mut running_worker_starts = vec![0u32; num_terms];

        for w in 0..pass1_results.len() {
            let mut ptrs = Vec::with_capacity(num_terms);
            for t in 0..num_terms {
                ptrs.push(postings_offsets[t] + running_worker_starts[t]);
                running_worker_starts[t] += pass1_results[w].term_counts[t];
            }
            worker_ptrs.push(ptrs);
        }

        let mut doc_offsets = vec![0u32; total_docs + 1];
        let mut doc_tokens = vec![SENTINEL_TOKEN_ID; total_tokens];
        let mut postings_data = vec![0u32; total_postings as usize];

        // PASS 2: Fill contiguous memory directly
        std::thread::scope(|s| {
            let mut doc_offsets_slice: &mut [u32] = &mut doc_offsets[..];
            let mut doc_tokens_slice: &mut [u16] = &mut doc_tokens[..];
            let postings_ptr = postings_data.as_mut_ptr() as usize;

            for (w_idx, chunk) in chunks.iter().enumerate() {
                let w_docs = pass1_results[w_idx].num_docs;
                let w_tokens = pass1_results[w_idx].total_tokens;
                let (w_doc_offsets, rem_docs) = doc_offsets_slice.split_at_mut(w_docs);
                let (w_doc_tokens, rem_tokens) = doc_tokens_slice.split_at_mut(w_tokens);
                doc_offsets_slice = rem_docs;
                doc_tokens_slice = rem_tokens;

                let vocab_ref = &vocab;
                let mut local_postings_ptrs = std::mem::take(&mut worker_ptrs[w_idx]);
                let token_base = worker_token_starts[w_idx] as u32;

                s.spawn(move || {
                    let postings_raw = postings_ptr as *mut u32;
                    let mut seen_in_doc = Vec::with_capacity(256);
                    let mut scratch = Vec::with_capacity(32);

                    let mut pos = 0;
                    let mut local_doc_idx = 0;
                    let mut local_token_idx = 0;

                    while pos < chunk.len() {
                        let line_start = pos;
                        while pos < chunk.len() && chunk[pos] != b'\n' {
                            pos += 1;
                        }
                        let mut line_end = pos;
                        if pos < chunk.len() && chunk[pos] == b'\n' {
                            pos += 1;
                        }
                        if line_end > line_start && chunk[line_end - 1] == b'\r' {
                            line_end -= 1;
                        }
                        let line = &chunk[line_start..line_end];
                        if line.is_empty() {
                            continue;
                        }

                        let tab_pos = match line.iter().position(|&b| b == b'\t') {
                            Some(p) => p,
                            None => continue,
                        };

                        let id_bytes = &line[..tab_pos];
                        let id_str = match std::str::from_utf8(id_bytes) {
                            Ok(s) => s,
                            Err(_) => continue,
                        };
                        let doc_id: u32 = match id_str.parse() {
                            Ok(id) => id,
                            Err(_) => continue,
                        };

                        let text = &line[tab_pos + 1..];
                        w_doc_offsets[local_doc_idx] = token_base + local_token_idx as u32;
                        seen_in_doc.clear();

                        for_each_token(text, &mut scratch, |tok| {
                            if let Some(tid) = vocab_ref.get_term_id(tok) {
                                let pid = vocab_ref.term_to_phrase_id[tid as usize];
                                w_doc_tokens[local_token_idx] = pid;
                                seen_in_doc.push(tid);
                            } else {
                                w_doc_tokens[local_token_idx] = SENTINEL_TOKEN_ID;
                            }
                            local_token_idx += 1;
                        });

                        seen_in_doc.sort_unstable();
                        seen_in_doc.dedup();

                        for &tid in &seen_in_doc {
                            let ptr_idx = tid as usize;
                            let out_pos = local_postings_ptrs[ptr_idx] as usize;
                            unsafe {
                                *postings_raw.add(out_pos) = doc_id;
                            }
                            local_postings_ptrs[ptr_idx] += 1;
                        }

                        local_doc_idx += 1;
                    }
                });
            }
        });

        doc_offsets[total_docs] = total_tokens as u32;

        let dense_threshold = (total_docs / 32).max(64);
        let mut dense_term_map = vec![None; num_terms];
        let mut num_dense = 0;
        for (tid, &count) in total_term_counts.iter().enumerate() {
            if count as usize >= dense_threshold {
                dense_term_map[tid] = Some(num_dense as u32);
                num_dense += 1;
            }
        }

        let words_per_bitset = (total_docs + 63) / 64;
        let mut dense_bitsets = vec![0u64; num_dense * words_per_bitset];

        for (tid, &dense_idx_opt) in dense_term_map.iter().enumerate() {
            if let Some(d_idx) = dense_idx_opt {
                let start_word = d_idx as usize * words_per_bitset;
                let post_start = postings_offsets[tid] as usize;
                let post_end = postings_offsets[tid + 1] as usize;
                let slice = &postings_data[post_start..post_end];
                for &doc_id in slice {
                    let id = doc_id as usize;
                    if id < total_docs {
                        dense_bitsets[start_word + (id / 64)] |= 1u64 << (id % 64);
                    }
                }
            }
        }

        Ok(Self {
            num_docs: total_docs,
            total_tokens,
            doc_offsets,
            doc_tokens,
            postings_offsets,
            postings_data,
            dense_bitsets,
            dense_term_map,
            words_per_bitset,
            vocab,
        })
    }
}

pub fn partition_docs_data(docs_data: &[u8], num_chunks: usize) -> Vec<&[u8]> {
    if docs_data.is_empty() || num_chunks <= 1 {
        return vec![docs_data];
    }

    let total_len = docs_data.len();
    let mut boundaries = Vec::with_capacity(num_chunks + 1);
    boundaries.push(0);

    for i in 1..num_chunks {
        let tentative = (i * total_len) / num_chunks;
        let mut b = tentative;
        while b < total_len && docs_data[b] != b'\n' {
            b += 1;
        }
        if b < total_len {
            b += 1;
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
        chunks.push(&docs_data[w[0]..w[1]]);
    }
    chunks
}

#[derive(Clone)]
pub struct BitSet {
    pub words: Vec<u64>,
    pub num_docs: usize,
}

impl BitSet {
    pub fn new(num_docs: usize) -> Self {
        let num_words = (num_docs + 63) / 64;
        Self {
            words: vec![0u64; num_words],
            num_docs,
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.words.fill(0);
    }

    #[inline]
    pub fn load_sparse(&mut self, list: &[u32]) {
        self.clear();
        for &doc_id in list {
            let id = doc_id as usize;
            if id < self.num_docs {
                self.words[id / 64] |= 1u64 << (id % 64);
            }
        }
    }

    #[inline]
    pub fn load_dense(&mut self, dense_words: &[u64]) {
        self.words.copy_from_slice(dense_words);
    }

    #[inline]
    pub fn union_sparse(&mut self, list: &[u32]) {
        for &doc_id in list {
            let id = doc_id as usize;
            if id < self.num_docs {
                self.words[id / 64] |= 1u64 << (id % 64);
            }
        }
    }

    #[inline]
    pub fn union_dense(&mut self, dense_words: &[u64]) {
        for (w1, w2) in self.words.iter_mut().zip(dense_words) {
            *w1 |= *w2;
        }
    }

    #[inline]
    pub fn intersect_with_sparse(&mut self, list: &[u32]) {
        let mut new_words = vec![0u64; self.words.len()];
        for &doc_id in list {
            let id = doc_id as usize;
            if id < self.num_docs {
                let w_idx = id / 64;
                let bit = 1u64 << (id % 64);
                if (self.words[w_idx] & bit) != 0 {
                    new_words[w_idx] |= bit;
                }
            }
        }
        self.words = new_words;
    }

    #[inline]
    pub fn intersect_with_dense(&mut self, dense_words: &[u64]) {
        for (w1, w2) in self.words.iter_mut().zip(dense_words) {
            *w1 &= *w2;
        }
    }

    #[inline]
    pub fn difference_with_sparse(&mut self, list: &[u32]) {
        for &doc_id in list {
            let id = doc_id as usize;
            if id < self.num_docs {
                self.words[id / 64] &= !(1u64 << (id % 64));
            }
        }
    }

    #[inline]
    pub fn difference_with_dense(&mut self, dense_words: &[u64]) {
        for (w1, w2) in self.words.iter_mut().zip(dense_words) {
            *w1 &= !*w2;
        }
    }

    pub fn summary(&self) -> (usize, u64, Vec<u32>) {
        let mut count = 0usize;
        let mut sum = 0u64;
        let mut first_10 = Vec::with_capacity(10);

        for (word_idx, &word) in self.words.iter().enumerate() {
            if word == 0 {
                continue;
            }
            let base_id = word_idx * 64;
            let mut w = word;
            while w != 0 {
                let bit_idx = w.trailing_zeros() as usize;
                let doc_id = base_id + bit_idx;
                if doc_id >= self.num_docs {
                    break;
                }
                count += 1;
                sum += doc_id as u64;
                if first_10.len() < 10 {
                    first_10.push(doc_id as u32);
                }
                w &= w - 1;
            }
        }
        (count, sum, first_10)
    }
}

fn format_result_into(count: usize, sum: u64, first_10: &[u32], output: &mut String) {
    if count == 0 {
        output.push_str("0 0\n");
    } else {
        write!(output, "{} {}", count, sum).unwrap();
        for &id in first_10 {
            write!(output, " {}", id).unwrap();
        }
        output.push('\n');
    }
}

pub struct QueryEvaluator {
    pub bitset: BitSet,
    pub candidate_docs: Vec<u32>,
    pub phrase_token_ids: Vec<u16>,
    pub matching_docs: Vec<u32>,
    pub sorted_and_terms: Vec<(usize, u32)>, // (cardinality, term_id)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoolOp {
    And,
    Or,
    Not,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParsedQuery {
    Bool {
        first_term: Vec<u8>,
        clauses: Vec<(BoolOp, Vec<u8>)>,
    },
    Phrase {
        terms: Vec<Vec<u8>>,
    },
    Empty,
}

pub fn parse_query_line(line: &[u8]) -> ParsedQuery {
    let line = if line.ends_with(b"\r") {
        &line[..line.len() - 1]
    } else {
        line
    };
    if line.is_empty() {
        return ParsedQuery::Empty;
    }
    if line.starts_with(b"BOOL ") {
        let rest = &line[5..];
        let mut parts = rest.split(|&b| b == b' ');
        let first_term = match parts.next() {
            Some(t) if !t.is_empty() => t.to_vec(),
            _ => return ParsedQuery::Empty,
        };
        let mut clauses = Vec::new();
        while let Some(op_bytes) = parts.next() {
            if op_bytes.is_empty() {
                continue;
            }
            let op = if op_bytes == b"AND" {
                BoolOp::And
            } else if op_bytes == b"OR" {
                BoolOp::Or
            } else if op_bytes == b"NOT" {
                BoolOp::Not
            } else {
                continue;
            };
            if let Some(term) = parts.next() {
                if !term.is_empty() {
                    clauses.push((op, term.to_vec()));
                }
            }
        }
        ParsedQuery::Bool {
            first_term,
            clauses,
        }
    } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") && line.len() >= 9 {
        let inner = &line[8..line.len() - 1];
        let terms: Vec<Vec<u8>> = inner
            .split(|&b| b == b' ')
            .filter(|t| !t.is_empty())
            .map(|t| t.to_vec())
            .collect();
        if terms.is_empty() {
            ParsedQuery::Empty
        } else {
            ParsedQuery::Phrase { terms }
        }
    } else {
        ParsedQuery::Empty
    }
}

pub fn parse_all_queries(queries_data: &[u8]) -> Vec<ParsedQuery> {
    let mut queries = Vec::new();
    for line in queries_data.split(|&b| b == b'\n') {
        let line = if line.ends_with(b"\r") {
            &line[..line.len() - 1]
        } else {
            line
        };
        if line.is_empty() {
            continue;
        }
        queries.push(parse_query_line(line));
    }
    queries
}

impl QueryEvaluator {
    pub fn new(num_docs: usize) -> Self {
        Self {
            bitset: BitSet::new(num_docs),
            candidate_docs: Vec::with_capacity(1024),
            phrase_token_ids: Vec::with_capacity(16),
            matching_docs: Vec::with_capacity(1024),
            sorted_and_terms: Vec::with_capacity(8),
        }
    }

    pub fn evaluate_parsed_query(
        &mut self,
        query: &ParsedQuery,
        corpus: &CorpusIndex,
        output: &mut String,
    ) {
        match query {
            ParsedQuery::Bool {
                first_term,
                clauses,
            } => {
                let is_pure_and = clauses.iter().all(|(op, _)| *op == BoolOp::And);

                if is_pure_and {
                    // PLANNER OPTIMIZATION: Collect all terms, sort by cardinality (rarest first)
                    self.sorted_and_terms.clear();

                    let first_tid = match corpus.vocab.get_term_id(first_term) {
                        Some(id) => id,
                        None => {
                            output.push_str("0 0\n");
                            return;
                        }
                    };
                    let first_len = corpus.get_posting_len(first_tid);
                    if first_len == 0 {
                        output.push_str("0 0\n");
                        return;
                    }
                    self.sorted_and_terms.push((first_len, first_tid));

                    for (_, term) in clauses {
                        let tid = match corpus.vocab.get_term_id(term) {
                            Some(id) => id,
                            None => {
                                output.push_str("0 0\n");
                                return;
                            }
                        };
                        let len = corpus.get_posting_len(tid);
                        if len == 0 {
                            output.push_str("0 0\n");
                            return;
                        }
                        self.sorted_and_terms.push((len, tid));
                    }

                    // Sort terms: smallest posting list first!
                    self.sorted_and_terms.sort_unstable_by_key(|&(len, _)| len);

                    // Load rarest term
                    let (_, rarest_tid) = self.sorted_and_terms[0];
                    match corpus.get_postings(rarest_tid) {
                        Some(PostingRef::Sparse(initial)) => {
                            self.candidate_docs.clear();
                            self.candidate_docs.extend_from_slice(initial);

                            for &(_, tid) in &self.sorted_and_terms[1..] {
                                if self.candidate_docs.is_empty() {
                                    break;
                                }
                                match corpus.get_postings(tid) {
                                    Some(PostingRef::Sparse(other)) => {
                                        // Galloping / binary search intersection
                                        self.candidate_docs
                                            .retain(|&id| other.binary_search(&id).is_ok());
                                    }
                                    Some(PostingRef::Dense(words)) => {
                                        // Direct bit test
                                        self.candidate_docs.retain(|&id| {
                                            let idx = id as usize;
                                            (words[idx / 64] & (1u64 << (idx % 64))) != 0
                                        });
                                    }
                                    None => {
                                        self.candidate_docs.clear();
                                        break;
                                    }
                                }
                            }

                            if self.candidate_docs.is_empty() {
                                output.push_str("0 0\n");
                            } else {
                                let count = self.candidate_docs.len();
                                let sum: u64 = self.candidate_docs.iter().map(|&id| id as u64).sum();
                                let limit = count.min(10);
                                format_result_into(count, sum, &self.candidate_docs[..limit], output);
                            }
                            return;
                        }
                        Some(PostingRef::Dense(words)) => {
                            // Rarest term is already dense -> all terms are dense!
                            self.bitset.load_dense(words);
                            for &(_, tid) in &self.sorted_and_terms[1..] {
                                match corpus.get_postings(tid) {
                                    Some(PostingRef::Dense(w)) => self.bitset.intersect_with_dense(w),
                                    Some(PostingRef::Sparse(s)) => self.bitset.intersect_with_sparse(s),
                                    None => {
                                        self.bitset.clear();
                                        break;
                                    }
                                }
                            }
                            let (count, sum, first_10) = self.bitset.summary();
                            format_result_into(count, sum, &first_10, output);
                            return;
                        }
                        None => {
                            output.push_str("0 0\n");
                            return;
                        }
                    }
                }

                // General mixed boolean query: Strictly evaluate left to right
                let first_id = corpus.vocab.get_term_id(first_term);
                let first_postings = first_id.and_then(|id| corpus.get_postings(id));

                match first_postings {
                    Some(PostingRef::Sparse(s)) => self.bitset.load_sparse(s),
                    Some(PostingRef::Dense(d)) => self.bitset.load_dense(d),
                    None => self.bitset.clear(),
                }

                for (op, term) in clauses {
                    let term_id = corpus.vocab.get_term_id(term);
                    let term_postings = term_id.and_then(|id| corpus.get_postings(id));

                    match (op, term_postings) {
                        (BoolOp::And, Some(PostingRef::Sparse(s))) => self.bitset.intersect_with_sparse(s),
                        (BoolOp::And, Some(PostingRef::Dense(d))) => self.bitset.intersect_with_dense(d),
                        (BoolOp::And, None) => self.bitset.clear(),

                        (BoolOp::Or, Some(PostingRef::Sparse(s))) => self.bitset.union_sparse(s),
                        (BoolOp::Or, Some(PostingRef::Dense(d))) => self.bitset.union_dense(d),
                        (BoolOp::Or, None) => {}

                        (BoolOp::Not, Some(PostingRef::Sparse(s))) => self.bitset.difference_with_sparse(s),
                        (BoolOp::Not, Some(PostingRef::Dense(d))) => self.bitset.difference_with_dense(d),
                        (BoolOp::Not, None) => {}
                    }
                }

                let (count, sum, first_10) = self.bitset.summary();
                format_result_into(count, sum, &first_10, output);
            }
            ParsedQuery::Phrase { terms } => {
                self.phrase_token_ids.clear();
                self.candidate_docs.clear();
                self.matching_docs.clear();

                if terms.is_empty() {
                    output.push_str("0 0\n");
                    return;
                }

                let mut rarest_tid = None;
                let mut min_len = usize::MAX;

                for t in terms {
                    if let Some(pid) = corpus.vocab.get_phrase_id(t) {
                        self.phrase_token_ids.push(pid);
                        if let Some(tid) = corpus.vocab.get_term_id(t) {
                            let len = corpus.get_posting_len(tid);
                            if len == 0 {
                                output.push_str("0 0\n");
                                return;
                            }
                            if len < min_len {
                                min_len = len;
                                rarest_tid = Some(tid);
                            }
                        } else {
                            output.push_str("0 0\n");
                            return;
                        }
                    } else {
                        output.push_str("0 0\n");
                        return;
                    }
                }

                let r_id = match rarest_tid {
                    Some(id) => id,
                    None => {
                        output.push_str("0 0\n");
                        return;
                    }
                };

                let initial = match corpus.get_sparse_postings(r_id) {
                    Some(p) => p,
                    None => {
                        output.push_str("0 0\n");
                        return;
                    }
                };

                self.candidate_docs.extend_from_slice(initial);

                for t in terms {
                    if let Some(tid) = corpus.vocab.get_term_id(t) {
                        if tid == r_id {
                            continue;
                        }
                        if let Some(postings) = corpus.get_sparse_postings(tid) {
                            self.candidate_docs
                                .retain(|doc_id| postings.binary_search(doc_id).is_ok());
                        } else {
                            output.push_str("0 0\n");
                            return;
                        }
                    }
                }

                let k = self.phrase_token_ids.len();
                let first_tok = self.phrase_token_ids[0];
                let target = &self.phrase_token_ids[..];

                for &doc_id in &self.candidate_docs {
                    let id = doc_id as usize;
                    let start = corpus.doc_offsets[id] as usize;
                    let end = corpus.doc_offsets[id + 1] as usize;
                    let doc_slice = &corpus.doc_tokens[start..end];

                    if doc_slice.len() >= k {
                        let mut pos = 0;
                        let max_pos = doc_slice.len() - k;
                        let mut found = false;
                        while pos <= max_pos {
                            if doc_slice[pos] == first_tok && &doc_slice[pos..pos + k] == target {
                                found = true;
                                break;
                            }
                            pos += 1;
                        }
                        if found {
                            self.matching_docs.push(doc_id);
                        }
                    }
                }

                let count = self.matching_docs.len();
                if count == 0 {
                    output.push_str("0 0\n");
                } else {
                    let sum: u64 = self.matching_docs.iter().map(|&id| id as u64).sum();
                    let limit = count.min(10);
                    format_result_into(count, sum, &self.matching_docs[..limit], output);
                }
            }
            ParsedQuery::Empty => {
                output.push_str("0 0\n");
            }
        }
    }
}

pub fn parallel_evaluate_queries(
    corpus: &CorpusIndex,
    queries: &[ParsedQuery],
    num_threads: usize,
) -> (Vec<String>, std::time::Duration, std::time::Duration) {
    if queries.is_empty() {
        return (Vec::new(), std::time::Duration::ZERO, std::time::Duration::ZERO);
    }

    let actual_threads = num_threads.max(1).min(queries.len());
    let next_query_idx = AtomicUsize::new(0);

    let thread_results: Vec<(Vec<(usize, String)>, u64, u64)> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(actual_threads);
        for _ in 0..actual_threads {
            let next_idx_ref = &next_query_idx;
            handles.push(s.spawn(move || {
                let mut evaluator = QueryEvaluator::new(corpus.num_docs);
                let mut local_results = Vec::with_capacity(queries.len() / actual_threads + 32);
                let mut buf = String::with_capacity(64);
                let mut bool_nanos = 0u64;
                let mut phrase_nanos = 0u64;

                loop {
                    let idx = next_idx_ref.fetch_add(1, AtomicOrdering::Relaxed);
                    if idx >= queries.len() {
                        break;
                    }
                    buf.clear();
                    let q = &queries[idx];
                    let t_start = std::time::Instant::now();
                    evaluator.evaluate_parsed_query(q, corpus, &mut buf);
                    let dt = t_start.elapsed().as_nanos() as u64;
                    match q {
                        ParsedQuery::Bool { .. } => bool_nanos += dt,
                        ParsedQuery::Phrase { .. } => phrase_nanos += dt,
                        ParsedQuery::Empty => {}
                    }
                    local_results.push((idx, buf.clone()));
                }

                (local_results, bool_nanos, phrase_nanos)
            }));
        }

        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut answers = vec![String::new(); queries.len()];
    let mut total_bool_nanos = 0u64;
    let mut total_phrase_nanos = 0u64;

    for (local_res, b_ns, p_ns) in thread_results {
        total_bool_nanos += b_ns;
        total_phrase_nanos += p_ns;
        for (idx, ans) in local_res {
            answers[idx] = ans;
        }
    }

    (
        answers,
        std::time::Duration::from_nanos(total_bool_nanos),
        std::time::Duration::from_nanos(total_phrase_nanos),
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let docs_path = Path::new(data_dir).join("docs.txt");
    let queries_path = Path::new(data_dir).join("queries.txt");

    if !docs_path.exists() || !queries_path.exists() {
        eprintln!(
            "Input files missing: {} or {}",
            docs_path.display(),
            queries_path.display()
        );
        std::process::exit(1);
    }

    let t0 = std::time::Instant::now();
    let queries_data = fs::read(&queries_path).expect("failed to read queries.txt");
    let docs_data = fs::read(&docs_path).expect("failed to read docs.txt");

    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        });

    let ingest_threads = env::var("INGEST_THREADS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(num_threads);

    let t_ingest_start = std::time::Instant::now();
    let vocab = QueryVocabularies::extract(&queries_data);
    let corpus = CorpusIndex::build(&docs_data, vocab, ingest_threads).expect("corpus index build failed");
    let parsed_queries = parse_all_queries(&queries_data);
    let t_ingest = t_ingest_start.elapsed();

    let t_q_start = std::time::Instant::now();
    let (results, t_bool_cpu, t_phrase_cpu) = parallel_evaluate_queries(&corpus, &parsed_queries, num_threads);
    let t_query = t_q_start.elapsed();

    let mut output_str = String::with_capacity(queries_data.len() * 2);
    for res in &results {
        output_str.push_str(res);
    }
    let output_bytes = output_str.into_bytes();

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create output dir");
    let out_file_path = out_dir_path.join("results.txt");

    let mut file = fs::File::create(&out_file_path).expect("failed to create results.txt");
    file.write_all(&output_bytes).expect("failed to write results.txt");
    file.flush().expect("failed to flush results.txt");

    let t_total = t0.elapsed();

    eprintln!(
        "Index pipeline [Prototype C, threads={}, ingest_threads={}]: docs={}, queries={}, vocab_entries={}, stored_postings={}, ingest={:?}, query_wall={:?}, total={:?}",
        num_threads, ingest_threads, corpus.num_docs, parsed_queries.len(), corpus.vocab.num_terms(), corpus.retained_postings_count(), t_ingest, t_query, t_total
    );
    eprintln!(
        "Query work breakdown (aggregate CPU): bool={:?}, phrase={:?}",
        t_bool_cpu, t_phrase_cpu
    );

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
    fn test_tokenizer_uppercase_and_lowercase() {
        assert_eq!(tokenize(b"The Quick BROWN fox 123"), vec![
            b"the".to_vec(),
            b"quick".to_vec(),
            b"brown".to_vec(),
            b"fox".to_vec(),
            b"123".to_vec(),
        ]);
    }

    #[test]
    fn test_tokenizer_zurich() {
        let text = "Zürich".as_bytes();
        assert_eq!(tokenize(text), vec![b"z".to_vec(), b"rich".to_vec()]);
    }

    #[test]
    fn test_tokenizer_naive() {
        let text = "naïve".as_bytes();
        assert_eq!(tokenize(text), vec![b"na".to_vec(), b"ve".to_vec()]);
    }

    #[test]
    fn test_tokenizer_habeas_corpus_punctuation() {
        assert_eq!(
            tokenize(b"habeas-corpus, court's, U.S.C."),
            vec![
                b"habeas".to_vec(),
                b"corpus".to_vec(),
                b"court".to_vec(),
                b"s".to_vec(),
                b"u".to_vec(),
                b"s".to_vec(),
                b"c".to_vec(),
            ]
        );
    }

    #[test]
    fn test_edge_cases_all_documents_empty_results_missing_terms() {
        let mut docs = Vec::new();
        for i in 0..20 {
            let parity = if i % 2 == 0 { "even" } else { "odd" };
            docs.extend_from_slice(format!("{}\tuniversal {}\n", i, parity).as_bytes());
        }

        let queries = b"BOOL universal\n\
BOOL missing\n\
BOOL universal NOT universal\n\
BOOL even OR odd\n\
PHRASE \"missing term here\"\n\
PHRASE \"universal universal\"\n";

        let vocab = QueryVocabularies::extract(queries);
        let corpus = CorpusIndex::build(&docs, vocab, 4).unwrap();
        let parsed_queries = parse_all_queries(queries);

        let (results, _, _) = parallel_evaluate_queries(&corpus, &parsed_queries, 4);

        assert_eq!(results[0], "20 190 0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(results[1], "0 0\n");
        assert_eq!(results[2], "0 0\n");
        assert_eq!(results[3], "20 190 0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(results[4], "0 0\n");
        assert_eq!(results[5], "0 0\n");
    }
}
