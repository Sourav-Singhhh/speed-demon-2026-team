use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;

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

pub fn extract_query_vocab(queries_data: &[u8]) -> HashSet<Vec<u8>> {
    let mut vocab = HashSet::new();
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
                    vocab.insert(part.to_vec());
                }
            }
        } else if line.starts_with(b"PHRASE \"") && line.ends_with(b"\"") && line.len() >= 9 {
            let inner = &line[8..line.len() - 1];
            for term in inner.split(|&b| b == b' ') {
                if !term.is_empty() {
                    vocab.insert(term.to_vec());
                }
            }
        }
    }
    vocab
}

pub struct VocabTable {
    pub map: HashMap<Vec<u8>, u32>,
    pub tokens: Vec<Vec<u8>>,
    pub is_queried: Vec<bool>,
}

impl VocabTable {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            tokens: Vec::new(),
            is_queried: Vec::new(),
        }
    }

    pub fn get_or_intern(&mut self, token: &[u8], query_vocab: &HashSet<Vec<u8>>) -> u32 {
        if let Some(&id) = self.map.get(token) {
            id
        } else {
            let id = self.tokens.len() as u32;
            let queried = query_vocab.contains(token);
            let tok_vec = token.to_vec();
            self.map.insert(tok_vec.clone(), id);
            self.tokens.push(tok_vec);
            self.is_queried.push(queried);
            id
        }
    }

    pub fn get_id(&self, token: &[u8]) -> Option<u32> {
        self.map.get(token).copied()
    }
}

pub struct CorpusIndex {
    pub num_docs: usize,
    pub total_tokens: usize,
    pub doc_offsets: Vec<u32>,
    pub doc_tokens: Vec<u32>,
    pub postings: HashMap<u32, Vec<u32>>,
    pub vocab: VocabTable,
    pub query_vocab_size: usize,
}

impl CorpusIndex {
    pub fn build(docs_data: &[u8], query_vocab: &HashSet<Vec<u8>>) -> Result<Self, String> {
        let mut vocab = VocabTable::new();
        let mut doc_offsets: Vec<u32> = Vec::with_capacity(300_000);
        let mut doc_tokens: Vec<u32> = Vec::with_capacity(37_000_000);
        let mut postings: HashMap<u32, Vec<u32>> = HashMap::with_capacity(query_vocab.len());

        let mut scratch = Vec::with_capacity(32);
        let mut seen_in_doc: Vec<u32> = Vec::with_capacity(256);
        let mut num_docs = 0;
        let mut total_tokens = 0;

        let mut pos = 0;
        while pos < docs_data.len() {
            let line_start = pos;
            while pos < docs_data.len() && docs_data[pos] != b'\n' {
                pos += 1;
            }
            let mut line_end = pos;
            if pos < docs_data.len() && docs_data[pos] == b'\n' {
                pos += 1;
            }
            if line_end > line_start && docs_data[line_end - 1] == b'\r' {
                line_end -= 1;
            }
            let line = &docs_data[line_start..line_end];
            if line.is_empty() {
                continue;
            }

            let tab_pos = line
                .iter()
                .position(|&b| b == b'\t')
                .ok_or_else(|| "missing TAB in doc line".to_string())?;

            let id_bytes = &line[..tab_pos];
            let id_str = std::str::from_utf8(id_bytes).map_err(|e| e.to_string())?;
            let doc_id: usize = id_str.parse().map_err(|e: std::num::ParseIntError| e.to_string())?;

            if doc_id != num_docs {
                return Err(format!("expected doc id {}, got {}", num_docs, doc_id));
            }

            let text = &line[tab_pos + 1..];
            doc_offsets.push(doc_tokens.len() as u32);
            seen_in_doc.clear();

            for_each_token(text, &mut scratch, |tok| {
                total_tokens += 1;
                let token_id = vocab.get_or_intern(tok, query_vocab);
                doc_tokens.push(token_id);

                if vocab.is_queried[token_id as usize] {
                    seen_in_doc.push(token_id);
                }
            });

            // Deduplicate queried terms within this document so doc_id is added once
            seen_in_doc.sort_unstable();
            seen_in_doc.dedup();

            for &token_id in &seen_in_doc {
                postings
                    .entry(token_id)
                    .or_insert_with(Vec::new)
                    .push(doc_id as u32);
            }

            num_docs += 1;
        }

        doc_offsets.push(doc_tokens.len() as u32);

        Ok(Self {
            num_docs,
            total_tokens,
            doc_offsets,
            doc_tokens,
            postings,
            vocab,
            query_vocab_size: query_vocab.len(),
        })
    }

    pub fn retained_postings_count(&self) -> usize {
        self.postings.values().map(|p| p.len()).sum()
    }
}

#[derive(Clone)]
pub struct BitSet {
    words: Vec<u64>,
    num_docs: usize,
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
    pub fn set_all(&mut self) {
        self.words.fill(u64::MAX);
        // Clear padding bits beyond num_docs
        let remainder = self.num_docs % 64;
        if remainder != 0 {
            let last_idx = self.words.len() - 1;
            let mask = (1u64 << remainder) - 1;
            self.words[last_idx] &= mask;
        }
    }

    #[inline]
    pub fn load_postings(&mut self, postings: Option<&[u32]>) {
        self.clear();
        if let Some(list) = postings {
            for &doc_id in list {
                let id = doc_id as usize;
                if id < self.num_docs {
                    self.words[id / 64] |= 1u64 << (id % 64);
                }
            }
        }
    }

    #[inline]
    pub fn union_postings(&mut self, postings: Option<&[u32]>) {
        if let Some(list) = postings {
            for &doc_id in list {
                let id = doc_id as usize;
                if id < self.num_docs {
                    self.words[id / 64] |= 1u64 << (id % 64);
                }
            }
        }
    }

    #[inline]
    pub fn intersect_with(&mut self, other: &BitSet) {
        for (w1, w2) in self.words.iter_mut().zip(&other.words) {
            *w1 &= *w2;
        }
    }

    #[inline]
    pub fn difference_with(&mut self, other: &BitSet) {
        for (w1, w2) in self.words.iter_mut().zip(&other.words) {
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
                w &= w - 1; // Clear lowest set bit
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
    pub bitset_res: BitSet,
    pub bitset_tmp: BitSet,
    pub candidate_docs: Vec<u32>,
    pub phrase_token_ids: Vec<u32>,
    pub matching_docs: Vec<u32>,
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
            bitset_res: BitSet::new(num_docs),
            bitset_tmp: BitSet::new(num_docs),
            candidate_docs: Vec::with_capacity(1024),
            phrase_token_ids: Vec::with_capacity(16),
            matching_docs: Vec::with_capacity(1024),
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
                let first_id = corpus.vocab.get_id(first_term);
                let first_postings =
                    first_id.and_then(|id| corpus.postings.get(&id).map(|v| &v[..]));
                self.bitset_res.load_postings(first_postings);

                for (op, term) in clauses {
                    let term_id = corpus.vocab.get_id(term);
                    let term_postings =
                        term_id.and_then(|id| corpus.postings.get(&id).map(|v| &v[..]));

                    match op {
                        BoolOp::And => {
                            self.bitset_tmp.load_postings(term_postings);
                            self.bitset_res.intersect_with(&self.bitset_tmp);
                        }
                        BoolOp::Or => {
                            self.bitset_res.union_postings(term_postings);
                        }
                        BoolOp::Not => {
                            self.bitset_tmp.load_postings(term_postings);
                            self.bitset_res.difference_with(&self.bitset_tmp);
                        }
                    }
                }

                let (count, sum, first_10) = self.bitset_res.summary();
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

                let mut rarest_token_id = None;
                let mut min_len = usize::MAX;

                for t in terms {
                    if let Some(id) = corpus.vocab.get_id(t) {
                        if let Some(postings) = corpus.postings.get(&id) {
                            self.phrase_token_ids.push(id);
                            if postings.len() < min_len {
                                min_len = postings.len();
                                rarest_token_id = Some(id);
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

                let rarest_id = match rarest_token_id {
                    Some(id) => id,
                    None => {
                        output.push_str("0 0\n");
                        return;
                    }
                };

                let initial_candidates = match corpus.postings.get(&rarest_id) {
                    Some(p) => p,
                    None => {
                        output.push_str("0 0\n");
                        return;
                    }
                };

                self.candidate_docs.extend_from_slice(initial_candidates);

                for &id in &self.phrase_token_ids {
                    if id == rarest_id {
                        continue;
                    }
                    if let Some(postings) = corpus.postings.get(&id) {
                        self.candidate_docs
                            .retain(|doc_id| postings.binary_search(doc_id).is_ok());
                    } else {
                        output.push_str("0 0\n");
                        return;
                    }
                }

                let k = self.phrase_token_ids.len();
                for &doc_id in &self.candidate_docs {
                    let id = doc_id as usize;
                    let start = corpus.doc_offsets[id] as usize;
                    let end = corpus.doc_offsets[id + 1] as usize;
                    let doc_slice = &corpus.doc_tokens[start..end];

                    if doc_slice.len() >= k
                        && doc_slice
                            .windows(k)
                            .any(|w| w == &self.phrase_token_ids[..])
                    {
                        self.matching_docs.push(doc_id);
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

    pub fn evaluate_query(&mut self, line: &[u8], corpus: &CorpusIndex, output: &mut String) {
        let query = parse_query_line(line);
        self.evaluate_parsed_query(&query, corpus, output);
    }
}

pub fn sequential_evaluate_queries(
    corpus: &CorpusIndex,
    queries: &[ParsedQuery],
) -> (Vec<String>, std::time::Duration, std::time::Duration) {
    let mut evaluator = QueryEvaluator::new(corpus.num_docs);
    let mut results = Vec::with_capacity(queries.len());
    let mut buf = String::with_capacity(64);
    let mut t_bool = std::time::Duration::ZERO;
    let mut t_phrase = std::time::Duration::ZERO;

    for query in queries {
        buf.clear();
        let t_start = std::time::Instant::now();
        evaluator.evaluate_parsed_query(query, corpus, &mut buf);
        let elapsed = t_start.elapsed();
        match query {
            ParsedQuery::Bool { .. } => t_bool += elapsed,
            ParsedQuery::Phrase { .. } => t_phrase += elapsed,
            ParsedQuery::Empty => {}
        }
        results.push(buf.clone());
    }

    (results, t_bool, t_phrase)
}

use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

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

pub fn execute_index_pipeline(docs_data: &[u8], queries_data: &[u8]) -> Result<Vec<u8>, String> {
    let query_vocab = extract_query_vocab(queries_data);
    let corpus = CorpusIndex::build(docs_data, &query_vocab)?;
    let parsed_queries = parse_all_queries(queries_data);

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    let (results, _, _) = parallel_evaluate_queries(&corpus, &parsed_queries, num_threads);

    let mut output = String::with_capacity(queries_data.len() * 2);
    for res in results {
        output.push_str(&res);
    }

    Ok(output.into_bytes())
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

    let t_ingest_start = std::time::Instant::now();
    let query_vocab = extract_query_vocab(&queries_data);
    let corpus = CorpusIndex::build(&docs_data, &query_vocab).expect("corpus index build failed");
    let parsed_queries = parse_all_queries(&queries_data);
    let t_ingest = t_ingest_start.elapsed();

    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        });

    let mode = env::var("QUERY_MODE").unwrap_or_else(|_| "parallel".to_string());

    let (results, t_query, t_bool_cpu, t_phrase_cpu) = if mode == "seq" {
        let t_q_start = std::time::Instant::now();
        let (r, tb, tp) = sequential_evaluate_queries(&corpus, &parsed_queries);
        (r, t_q_start.elapsed(), tb, tp)
    } else {
        let t_q_start = std::time::Instant::now();
        let (r, tb, tp) = parallel_evaluate_queries(&corpus, &parsed_queries, num_threads);
        (r, t_q_start.elapsed(), tb, tp)
    };

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
        "Index pipeline [mode={}, threads={}]: docs={}, queries={}, ingest={:?}, query_wall={:?}, total={:?}",
        mode, num_threads, corpus.num_docs, parsed_queries.len(), t_ingest, t_query, t_total
    );
    eprintln!(
        "Query work breakdown (aggregate CPU): bool={:?}, phrase={:?}",
        t_bool_cpu, t_phrase_cpu
    );

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
    fn test_tokenizer_case_007_distinct_from_7() {
        let t1 = tokenize(b"Case 007");
        let t2 = tokenize(b"Case 7");
        assert_eq!(t1, vec![b"case".to_vec(), b"007".to_vec()]);
        assert_eq!(t2, vec![b"case".to_vec(), b"7".to_vec()]);
        assert_ne!(t1[1], t2[1]);
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
    fn test_tokenizer_em_dash_and_utf8_bytes() {
        let text = "bail—bond".as_bytes();
        assert_eq!(tokenize(text), vec![b"bail".to_vec(), b"bond".to_vec()]);
    }

    #[test]
    fn test_tokenizer_empty_and_separators_only() {
        assert!(tokenize(b"").is_empty());
        assert!(tokenize(b"   ").is_empty());
        assert!(tokenize(b",.;:!@#$%^&*()_+-=").is_empty());
        assert!(tokenize("§§ ¶ — ***".as_bytes()).is_empty());
    }

    #[test]
    fn test_tokenizer_consecutive_and_trailing_separators() {
        assert_eq!(
            tokenize(b"...word1,,,,word2---"),
            vec![b"word1".to_vec(), b"word2".to_vec()]
        );
    }

    #[test]
    fn test_token_position_preservation_with_non_queried_terms() {
        let mut query_vocab = HashSet::new();
        query_vocab.insert(b"bail".to_vec());
        query_vocab.insert(b"bond".to_vec());

        let docs_data = b"0\tbail bond\n1\tbail unqueried bond\n";
        let corpus = CorpusIndex::build(docs_data, &query_vocab).unwrap();

        assert_eq!(corpus.num_docs, 2);

        let d0_start = corpus.doc_offsets[0] as usize;
        let d0_end = corpus.doc_offsets[1] as usize;
        let d0_tokens = &corpus.doc_tokens[d0_start..d0_end];
        assert_eq!(d0_tokens.len(), 2);

        let d1_start = corpus.doc_offsets[1] as usize;
        let d1_end = corpus.doc_offsets[2] as usize;
        let d1_tokens = &corpus.doc_tokens[d1_start..d1_end];
        assert_eq!(d1_tokens.len(), 3);

        let bail_id = corpus.vocab.get_id(b"bail").unwrap();
        let bond_id = corpus.vocab.get_id(b"bond").unwrap();
        let unqueried_id = corpus.vocab.get_id(b"unqueried").unwrap();

        assert_eq!(d0_tokens, &[bail_id, bond_id]);
        assert_eq!(d1_tokens, &[bail_id, unqueried_id, bond_id]);

        let phrase = [bail_id, bond_id];
        assert!(d0_tokens.windows(2).any(|w| w == phrase));
        assert!(!d1_tokens.windows(2).any(|w| w == phrase));
    }

    #[test]
    fn test_worked_example_end_to_end() {
        let docs = b"0\tThe surety posted bail; the BAIL BOND was forfeited.\n\
1\tWrit of Habeas-Corpus: see 42 U.S.C. \xC2\xA7 1983 (bail bond).\n\
2\t\n\
3\tZ\xC3\xBCrich bail\xE2\x80\x94bond, bail bail bond. Case 007.\n\
4\tIn the matter of the estate. Bond not posted, No. 7.\n";

        let queries = b"BOOL bail AND bond\n\
BOOL bail\n\
BOOL estate OR surety AND bail\n\
BOOL bond NOT bail\n\
BOOL bail NOT bail\n\
BOOL zurich\n\
BOOL rich AND z\n\
BOOL not AND bond\n\
BOOL 7\n\
BOOL the OR writ OR case\n\
PHRASE \"bail bond\"\n\
PHRASE \"bail bail bond\"\n\
PHRASE \"bond bail\"\n\
PHRASE \"habeas corpus\"\n\
PHRASE \"u s c 1983\"\n\
PHRASE \"estate bond\"\n\
PHRASE \"forfeited writ\"\n\
PHRASE \"in the matter of\"\n";

        let expected = b"3 4 0 1 3\n\
3 4 0 1 3\n\
1 0 0\n\
1 4 4\n\
0 0\n\
0 0\n\
1 3 3\n\
1 4 4\n\
1 4 4\n\
4 8 0 1 3 4\n\
3 4 0 1 3\n\
1 3 3\n\
1 3 3\n\
1 1 1\n\
1 1 1\n\
1 4 4\n\
0 0\n\
1 4 4\n";

        let out = execute_index_pipeline(docs, queries).unwrap();
        assert_eq!(out, expected);
    }

    #[test]
    fn test_boolean_operations_and_precedence() {
        let docs = b"0\ta b\n1\ta c\n2\tb c\n3\td\n";
        let queries = b"BOOL a AND b\nBOOL a OR b\nBOOL a NOT b\nBOOL b OR d AND a\n";
        let expected = b"1 0 0\n3 3 0 1 2\n1 1 1\n1 0 0\n";
        let out = execute_index_pipeline(docs, queries).unwrap();
        assert_eq!(out, expected);
    }

    #[test]
    fn test_phrases_repeated_words_and_boundary() {
        let docs = b"0\tvery very good test\n1\tvery good\n2\t\n3\tgood very very\n";
        let queries = b"PHRASE \"very very good\"\nPHRASE \"very good\"\nPHRASE \"missing word\"\n";
        let expected = b"1 0 0\n2 1 0 1\n0 0\n";
        let out = execute_index_pipeline(docs, queries).unwrap();
        assert_eq!(out, expected);
    }

    #[test]
    fn test_output_formatting_more_than_ten_matches() {
        let mut docs = Vec::new();
        for i in 0..15 {
            docs.extend_from_slice(format!("{}\tx\n", i).as_bytes());
        }
        let queries = b"BOOL x\n";
        let expected = b"15 105 0 1 2 3 4 5 6 7 8 9\n";
        let out = execute_index_pipeline(&docs, queries).unwrap();
        assert_eq!(out, expected);
    }

    #[test]
    fn test_differential_sequential_versus_parallel() {
        // Diverse corpus covering empty docs, repeated terms, punctuation, varied lengths, > 10 matches
        let mut docs_vec = Vec::new();
        for i in 0..30 {
            if i % 5 == 0 {
                docs_vec.extend_from_slice(format!("{}\t\n", i).as_bytes());
            } else if i % 3 == 0 {
                docs_vec.extend_from_slice(format!("{}\tapple banana apple cherry common\n", i).as_bytes());
            } else {
                docs_vec.extend_from_slice(format!("{}\tbanana cherry common dog elephant {}\n", i, i).as_bytes());
            }
        }

        let queries_vec = b"BOOL common\n\
BOOL common AND banana\n\
BOOL common OR dog\n\
BOOL common NOT apple\n\
BOOL nonexisting\n\
BOOL apple AND nonexisting\n\
BOOL common OR nonexisting\n\
PHRASE \"apple banana apple\"\n\
PHRASE \"apple cherry common\"\n\
PHRASE \"banana cherry common\"\n\
PHRASE \"nonexisting phrase\"\n\
PHRASE \"common nonexistent\"\n\
BOOL 1 OR 2 OR 3\n\
BOOL common AND dog NOT apple\n";

        let query_vocab = extract_query_vocab(queries_vec);
        let corpus = CorpusIndex::build(&docs_vec, &query_vocab).unwrap();
        let parsed_queries = parse_all_queries(queries_vec);

        let (seq_results, _, _) = sequential_evaluate_queries(&corpus, &parsed_queries);

        for threads in [1, 2, 4, 8] {
            let (par_results, _, _) = parallel_evaluate_queries(&corpus, &parsed_queries, threads);
            assert_eq!(
                seq_results, par_results,
                "Sequential vs parallel results differed with {} threads!",
                threads
            );
        }
    }

    #[test]
    fn test_parallel_preserves_query_order() {
        let docs = b"0\talpha beta gamma\n1\tbeta gamma delta\n2\talpha delta\n";
        let mut queries = Vec::new();
        for i in 0..100 {
            if i % 3 == 0 {
                queries.extend_from_slice(b"BOOL alpha AND beta\n");
            } else if i % 3 == 1 {
                queries.extend_from_slice(b"PHRASE \"beta gamma\"\n");
            } else {
                queries.extend_from_slice(b"BOOL delta NOT alpha\n");
            }
        }

        let query_vocab = extract_query_vocab(&queries);
        let corpus = CorpusIndex::build(docs, &query_vocab).unwrap();
        let parsed_queries = parse_all_queries(&queries);

        let (seq_results, _, _) = sequential_evaluate_queries(&corpus, &parsed_queries);
        let (par_results, _, _) = parallel_evaluate_queries(&corpus, &parsed_queries, 6);

        assert_eq!(seq_results.len(), 100);
        assert_eq!(seq_results, par_results);
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

        let query_vocab = extract_query_vocab(queries);
        let corpus = CorpusIndex::build(&docs, &query_vocab).unwrap();
        let parsed_queries = parse_all_queries(queries);

        let (seq_results, _, _) = sequential_evaluate_queries(&corpus, &parsed_queries);
        let (par_results, _, _) = parallel_evaluate_queries(&corpus, &parsed_queries, 4);

        assert_eq!(seq_results, par_results);

        // universal matches all 20 docs: count=20, sum=0+1+..+19 = 190, first 10: 0..9
        assert_eq!(seq_results[0], "20 190 0 1 2 3 4 5 6 7 8 9\n");
        // missing matches 0
        assert_eq!(seq_results[1], "0 0\n");
        // universal NOT universal matches 0
        assert_eq!(seq_results[2], "0 0\n");
        // even OR odd matches all 20 docs
        assert_eq!(seq_results[3], "20 190 0 1 2 3 4 5 6 7 8 9\n");
        // missing term phrase matches 0
        assert_eq!(seq_results[4], "0 0\n");
        // repeated universal is never consecutive -> 0
        assert_eq!(seq_results[5], "0 0\n");
    }

    #[test]
    fn test_worker_panic_propagation() {
        // Verify that join().unwrap() properly propagates panics and never fails silently
        let res = std::panic::catch_unwind(|| {
            std::thread::scope(|s| {
                let handle = s.spawn(|| {
                    panic!("intentional worker failure");
                });
                handle.join().unwrap();
            });
        });
        assert!(res.is_err(), "Worker panic must propagate to caller!");
    }
}
