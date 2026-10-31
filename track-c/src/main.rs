use std::collections::HashMap;
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;

const BOM: &[u8] = b"\xEF\xBB\xBF";
pub const REGION_SPACE_LIMIT: usize = 1_000_000;
pub const UNMATCHED_SENTINEL_U8: u8 = 255;

pub fn parse_u64(s: &[u8]) -> Result<u64, String> {
    if s.is_empty() {
        return Err("empty integer".to_string());
    }
    let mut val: u64 = 0;
    for &b in s {
        if !b.is_ascii_digit() {
            return Err("non-digit in integer".to_string());
        }
        val = val
            .checked_mul(10)
            .and_then(|v| v.checked_add((b - b'0') as u64))
            .ok_or_else(|| "integer overflow".to_string())?;
    }
    Ok(val)
}

pub fn parse_cents(s: &[u8]) -> Result<i64, String> {
    if s.is_empty() {
        return Err("empty amount".to_string());
    }
    let (neg, s) = if s[0] == b'-' {
        (true, &s[1..])
    } else {
        (false, s)
    };
    let dot = s.iter().position(|&b| b == b'.').ok_or_else(|| "missing '.' in amount".to_string())?;
    if dot == 0 || dot + 3 != s.len() {
        return Err("invalid amount format".to_string());
    }
    let dollars: i64 = parse_u64(&s[..dot])? as i64;
    let d1 = (s[dot + 1] - b'0') as i64;
    let d2 = (s[dot + 2] - b'0') as i64;
    let cents = dollars * 100 + d1 * 10 + d2;
    Ok(if neg { -cents } else { cents })
}

pub fn format_cents(cents: i64) -> String {
    let mut out = String::with_capacity(16);
    format_cents_into(cents, &mut out);
    out
}

pub fn format_cents_into(cents: i64, out: &mut String) {
    if cents < 0 {
        out.push('-');
    }
    let abs_val: u64 = cents.unsigned_abs();
    let dollars = abs_val / 100;
    let rem = abs_val % 100;
    write!(out, "{}.{:02}", dollars, rem).unwrap();
}

pub struct RecordParser<'a> {
    data: &'a [u8],
    pos: usize,
    scratch: Vec<u8>,
}

impl<'a> RecordParser<'a> {
    pub fn new(data: &'a [u8]) -> Result<Self, String> {
        Self::new_with_header(data, true)
    }

    pub fn new_chunk(data: &'a [u8]) -> Result<Self, String> {
        Self::new_with_header(data, false)
    }

    pub fn new_with_header(data: &'a [u8], has_header: bool) -> Result<Self, String> {
        let mut pos = 0;
        if data.starts_with(BOM) {
            pos += 3;
        }
        if has_header {
            let header_prefix = b"id,name,note,region_id,amount";
            if !data[pos..].starts_with(header_prefix) {
                return Err("invalid header prefix".to_string());
            }
            pos += header_prefix.len();
            if data[pos..].starts_with(b"\r\n") {
                pos += 2;
            } else if data[pos..].starts_with(b"\n") {
                pos += 1;
            } else {
                return Err("invalid header terminator".to_string());
            }
        }
        Ok(Self {
            data,
            pos,
            scratch: Vec::with_capacity(256),
        })
    }

    pub fn next_record<F>(&mut self, mut on_record: F) -> Result<usize, String>
    where
        F: FnMut(u64, &[u8], usize, usize, u64, i64) -> Result<(), String>,
    {
        let mut count = 0;
        while self.pos < self.data.len() {
            // Mid-file BOM can only appear at record boundary
            if self.data[self.pos..].starts_with(BOM) {
                self.pos += 3;
            }

            // Field 0: id (unquoted integer)
            let start_id = self.pos;
            while self.pos < self.data.len() && self.data[self.pos].is_ascii_digit() {
                self.pos += 1;
            }
            if self.pos == start_id {
                return Err(format!("missing id at pos {}", self.pos));
            }
            let id = parse_u64(&self.data[start_id..self.pos])?;
            if self.pos >= self.data.len() || self.data[self.pos] != b',' {
                return Err(format!("expected ',' after id at pos {}", self.pos));
            }
            self.pos += 1;

            // Field 1: name (quoted or unquoted empty)
            let (name_bytes, name_slice): (usize, &[u8]) = if self.pos < self.data.len() && self.data[self.pos] == b',' {
                (0, &[])
            } else if self.pos < self.data.len() && self.data[self.pos] == b'"' {
                self.pos += 1;
                let start_name = self.pos;
                let mut unescaped_len = 0;
                let mut has_escapes = false;
                while self.pos < self.data.len() {
                    let b = self.data[self.pos];
                    if b == b'"' {
                        if self.pos + 1 < self.data.len() && self.data[self.pos + 1] == b'"' {
                            has_escapes = true;
                            unescaped_len += 1;
                            self.pos += 2;
                        } else {
                            self.pos += 1;
                            break;
                        }
                    } else {
                        unescaped_len += 1;
                        self.pos += 1;
                    }
                }
                if has_escapes {
                    self.scratch.clear();
                    self.scratch.reserve(unescaped_len);
                    let mut i = start_name;
                    while i < self.pos - 1 {
                        if self.data[i] == b'"' && self.data[i + 1] == b'"' {
                            self.scratch.push(b'"');
                            i += 2;
                        } else {
                            self.scratch.push(self.data[i]);
                            i += 1;
                        }
                    }
                    (unescaped_len, &self.scratch)
                } else {
                    let raw_slice = &self.data[start_name..self.pos - 1];
                    (unescaped_len, raw_slice)
                }
            } else {
                return Err(format!("unexpected byte in name at pos {}", self.pos));
            };

            if self.pos >= self.data.len() || self.data[self.pos] != b',' {
                return Err(format!("expected ',' after name at pos {}", self.pos));
            }
            self.pos += 1;

            // Field 2: note (quoted or unquoted empty)
            let note_bytes: usize = if self.pos < self.data.len() && self.data[self.pos] == b',' {
                0
            } else if self.pos < self.data.len() && self.data[self.pos] == b'"' {
                self.pos += 1;
                let mut unescaped_len = 0;
                while self.pos < self.data.len() {
                    let b = self.data[self.pos];
                    if b == b'"' {
                        if self.pos + 1 < self.data.len() && self.data[self.pos + 1] == b'"' {
                            unescaped_len += 1;
                            self.pos += 2;
                        } else {
                            self.pos += 1;
                            break;
                        }
                    } else {
                        unescaped_len += 1;
                        self.pos += 1;
                    }
                }
                unescaped_len
            } else {
                return Err(format!("unexpected byte in note at pos {}", self.pos));
            };

            if self.pos >= self.data.len() || self.data[self.pos] != b',' {
                return Err(format!("expected ',' after note at pos {}", self.pos));
            }
            self.pos += 1;

            // Field 3: region_id (unquoted integer)
            let start_reg = self.pos;
            while self.pos < self.data.len() && self.data[self.pos].is_ascii_digit() {
                self.pos += 1;
            }
            if self.pos == start_reg {
                return Err(format!("missing region_id at pos {}", self.pos));
            }
            let region_id = parse_u64(&self.data[start_reg..self.pos])?;
            if self.pos >= self.data.len() || self.data[self.pos] != b',' {
                return Err(format!("expected ',' after region_id at pos {}", self.pos));
            }
            self.pos += 1;

            // Field 4: amount (unquoted signed decimal)
            let start_amount = self.pos;
            while self.pos < self.data.len() && self.data[self.pos] != b'\r' && self.data[self.pos] != b'\n' {
                self.pos += 1;
            }
            let cents = parse_cents(&self.data[start_amount..self.pos])?;

            // Record terminator: CRLF, LF, or EOF
            if self.data[self.pos..].starts_with(b"\r\n") {
                self.pos += 2;
            } else if self.data[self.pos..].starts_with(b"\n") {
                self.pos += 1;
            } else if self.pos == self.data.len() {
                // EOF
            } else {
                return Err(format!("expected record terminator at pos {}", self.pos));
            }

            count += 1;
            on_record(id, name_slice, name_bytes, note_bytes, region_id, cents)?;
        }
        Ok(count)
    }
}

pub struct RegionTable {
    table: Box<[u8]>,
    pub countries: Vec<Vec<u8>>,
    pub unmatched_idx: usize,
    pub max_region_id: usize,
}

impl RegionTable {
    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
        let mut lines = data.split(|&b| b == b'\n');
        let header = lines.next().ok_or_else(|| "empty regions.csv".to_string())?;
        let header = if header.ends_with(b"\r") {
            &header[..header.len() - 1]
        } else {
            header
        };
        if header != b"region_id,country" {
            return Err("invalid regions.csv header".to_string());
        }

        let mut country_map: HashMap<Vec<u8>, usize> = HashMap::new();
        let mut countries: Vec<Vec<u8>> = Vec::new();
        let mut raw_regions: Vec<(usize, usize)> = Vec::new();
        let mut max_region_id = 0;

        for line in lines {
            let line = if line.ends_with(b"\r") {
                &line[..line.len() - 1]
            } else {
                line
            };
            if line.is_empty() {
                continue;
            }
            let comma = line
                .iter()
                .position(|&b| b == b',')
                .ok_or_else(|| "invalid line in regions.csv".to_string())?;
            let region_id = parse_u64(&line[..comma])? as usize;
            let country_code = &line[comma + 1..];
            if country_code.is_empty() {
                return Err("empty country code in regions.csv".to_string());
            }

            max_region_id = max_region_id.max(region_id);

            let next_idx = country_map.len();
            let c_idx = *country_map.entry(country_code.to_vec()).or_insert_with(|| {
                countries.push(country_code.to_vec());
                next_idx
            });
            raw_regions.push((region_id, c_idx));
        }

        let unmatched_idx = countries.len();
        countries.push(b"_UNMATCHED".to_vec());

        if unmatched_idx > 254 {
            return Err("country count exceeds u8 capacity".to_string());
        }

        let mut table = vec![UNMATCHED_SENTINEL_U8; REGION_SPACE_LIMIT].into_boxed_slice();
        for (rid, c_idx) in raw_regions {
            if rid < REGION_SPACE_LIMIT {
                table[rid] = c_idx as u8;
            }
        }

        Ok(Self {
            table,
            countries,
            unmatched_idx,
            max_region_id,
        })
    }

    #[inline(always)]
    pub fn lookup(&self, region_id: u64) -> usize {
        let rid = region_id as usize;
        if rid < REGION_SPACE_LIMIT {
            let c_idx = self.table[rid];
            if c_idx == UNMATCHED_SENTINEL_U8 {
                self.unmatched_idx
            } else {
                c_idx as usize
            }
        } else {
            self.unmatched_idx
        }
    }
}

const NAME_EMPTY_SENTINEL: u32 = u32::MAX;

#[derive(Clone, Copy)]
pub struct NameSlot {
    pub hash_tag: u32,
    pub offset: u32,
    pub len: u32,
    pub name_id: u32,
}

impl Default for NameSlot {
    fn default() -> Self {
        Self {
            hash_tag: 0,
            offset: 0,
            len: 0,
            name_id: NAME_EMPTY_SENTINEL,
        }
    }
}

#[derive(Clone, Copy)]
pub struct NameEntry {
    pub offset: u32,
    pub len: u32,
    pub hash: u64,
}

#[inline(always)]
pub fn hash_name_u64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51afd7ed558ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ceb9fe1a85ec53);
    h ^= h >> 33;
    h
}

#[inline(always)]
pub fn hash_tag_from_u64(h: u64) -> u32 {
    (h ^ (h >> 32)) as u32
}

pub struct NamePool {
    slots: Box<[NameSlot]>,
    arena: Vec<u8>,
    entries: Vec<NameEntry>,
    count: usize,
    mask: usize,
}

impl NamePool {
    pub fn new() -> Self {
        let initial_cap = 1024;
        Self {
            slots: vec![NameSlot::default(); initial_cap].into_boxed_slice(),
            arena: Vec::with_capacity(64 * 1024),
            entries: Vec::with_capacity(1024),
            count: 0,
            mask: initial_cap - 1,
        }
    }

    #[inline]
    pub fn intern(&mut self, name: &[u8]) -> u32 {
        let h64 = hash_name_u64(name);
        self.intern_with_hash(name, h64)
    }

    #[inline]
    pub fn intern_with_hash(&mut self, name: &[u8], h64: u64) -> u32 {
        let tag = hash_tag_from_u64(h64);
        let mut idx = (h64 as usize) & self.mask;

        loop {
            let slot = self.slots[idx];
            if slot.name_id == NAME_EMPTY_SENTINEL {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern_with_hash(name, h64);
                }

                let offset = u32::try_from(self.arena.len()).expect("arena offset overflow");
                let len = u32::try_from(name.len()).expect("name length overflow");
                self.arena.extend_from_slice(name);

                let id = self.count as u32;
                self.slots[idx] = NameSlot {
                    hash_tag: tag,
                    offset,
                    len,
                    name_id: id,
                };
                self.entries.push(NameEntry {
                    offset,
                    len,
                    hash: h64,
                });
                self.count += 1;
                return id;
            }

            if slot.hash_tag == tag && slot.len as usize == name.len() {
                let start = slot.offset as usize;
                let end = start + slot.len as usize;
                if &self.arena[start..end] == name {
                    return slot.name_id;
                }
            }

            idx = (idx + 1) & self.mask;
        }
    }

    fn grow(&mut self) {
        let new_cap = self.slots.len() * 2;
        let new_mask = new_cap - 1;
        let mut new_slots = vec![NameSlot::default(); new_cap].into_boxed_slice();

        for slot in self.slots.iter() {
            if slot.name_id != NAME_EMPTY_SENTINEL {
                let h64 = self.entries[slot.name_id as usize].hash;
                let mut idx = (h64 as usize) & new_mask;
                while new_slots[idx].name_id != NAME_EMPTY_SENTINEL {
                    idx = (idx + 1) & new_mask;
                }
                new_slots[idx] = *slot;
            }
        }

        self.slots = new_slots;
        self.mask = new_mask;
    }

    #[inline]
    pub fn get_name(&self, id: u32) -> &[u8] {
        let entry = self.entries[id as usize];
        let start = entry.offset as usize;
        let end = start + entry.len as usize;
        &self.arena[start..end]
    }

    #[inline]
    pub fn get_name_and_hash(&self, id: u32) -> (&[u8], u64) {
        let entry = self.entries[id as usize];
        let start = entry.offset as usize;
        let end = start + entry.len as usize;
        (&self.arena[start..end], entry.hash)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.count
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    pub fn arena_len(&self) -> usize {
        self.arena.len()
    }
}

pub struct CountryAccumulator {
    pub code: Vec<u8>,
    pub count: u64,
    pub id_sum: u64,
    pub amount_sum: i64,
    pub amount_min: Option<i64>,
    pub amount_max: Option<i64>,
    pub name_bytes: u64,
    pub note_bytes: u64,
    pub seen_names: Vec<u64>,
}

impl CountryAccumulator {
    pub fn new(code: Vec<u8>) -> Self {
        Self {
            code,
            count: 0,
            id_sum: 0,
            amount_sum: 0,
            amount_min: None,
            amount_max: None,
            name_bytes: 0,
            note_bytes: 0,
            seen_names: Vec::new(),
        }
    }

    #[inline]
    pub fn add(&mut self, record_id: u64, name_id: u32, name_len: usize, note_len: usize, cents: i64) {
        self.count += 1;
        self.id_sum += record_id;
        self.amount_sum += cents;
        self.amount_min = Some(match self.amount_min {
            Some(cur) => cur.min(cents),
            None => cents,
        });
        self.amount_max = Some(match self.amount_max {
            Some(cur) => cur.max(cents),
            None => cents,
        });
        self.name_bytes += name_len as u64;
        self.note_bytes += note_len as u64;

        let word_idx = (name_id / 64) as usize;
        let bit_mask = 1u64 << (name_id % 64);
        if word_idx >= self.seen_names.len() {
            self.seen_names.resize(word_idx + 1, 0);
        }
        self.seen_names[word_idx] |= bit_mask;
    }

    pub fn distinct_names_count(&self) -> u64 {
        self.seen_names
            .iter()
            .map(|&w| w.count_ones() as u64)
            .sum()
    }

    pub fn format_line(&self, out: &mut String) {
        let code_str = std::str::from_utf8(&self.code).unwrap_or("_ERR");
        let min_str = self
            .amount_min
            .map(format_cents)
            .unwrap_or_else(|| "0.00".to_string());
        let max_str = self
            .amount_max
            .map(format_cents)
            .unwrap_or_else(|| "0.00".to_string());
        let sum_str = format_cents(self.amount_sum);
        let distinct = self.distinct_names_count();

        writeln!(
            out,
            "{} {} {} {} {} {} {} {} {}",
            code_str,
            self.count,
            self.id_sum,
            sum_str,
            min_str,
            max_str,
            distinct,
            self.name_bytes,
            self.note_bytes
        )
        .unwrap();
    }
}

pub fn find_chunk_boundaries(data: &[u8], num_chunks: usize) -> Vec<usize> {
    if num_chunks <= 1 || data.is_empty() {
        return vec![0, data.len()];
    }

    let chunk_size = data.len() / num_chunks;
    if chunk_size == 0 {
        return vec![0, data.len()];
    }

    let mut boundaries = Vec::with_capacity(num_chunks + 1);
    boundaries.push(0);

    for i in 1..num_chunks {
        let nominal = i * chunk_size;
        let mut found = None;

        if nominal < data.len() {
            let mut j = nominal;
            while j + 1 < data.len() {
                if data[j] == b'\r' && data[j + 1] == b'\n' {
                    let boundary = j + 2;
                    found = Some(boundary);
                    break;
                }
                j += 1;
            }
        }

        let b = found.unwrap_or(data.len());
        if b > *boundaries.last().unwrap() && b < data.len() {
            boundaries.push(b);
        }
    }

    if *boundaries.last().unwrap() < data.len() {
        boundaries.push(data.len());
    }

    boundaries
}

pub struct WorkerAccumulator {
    pub country_aggs: Vec<CountryAccumulator>,
    pub name_pool: NamePool,
}

pub fn parse_chunk_worker(
    chunk_data: &[u8],
    is_first_chunk: bool,
    region_table: &RegionTable,
) -> Result<WorkerAccumulator, String> {
    let mut country_aggs: Vec<CountryAccumulator> = region_table
        .countries
        .iter()
        .map(|code| CountryAccumulator::new(code.clone()))
        .collect();

    let mut name_pool = NamePool::new();
    let mut parser = RecordParser::new_with_header(chunk_data, is_first_chunk)?;

    parser.next_record(|id, name_slice, name_bytes, note_bytes, region_id, cents| {
        let country_idx = region_table.lookup(region_id);
        let name_id = name_pool.intern(name_slice);
        country_aggs[country_idx].add(id, name_id, name_bytes, note_bytes, cents);
        Ok(())
    })?;

    Ok(WorkerAccumulator {
        country_aggs,
        name_pool,
    })
}

pub fn merge_single_worker(
    global_aggs: &mut [CountryAccumulator],
    global_name_pool: &mut NamePool,
    w: WorkerAccumulator,
    merge_intern_secs: &mut f64,
    merge_bitset_secs: &mut f64,
    merge_dealloc_secs: &mut f64,
) {
    let kw = w.name_pool.len();
    if kw > 0 {
        let t0 = std::time::Instant::now();
        // Build translation table from worker w local ID to Global ID using pre-computed hash
        let mut trans = Vec::with_capacity(kw);
        for id in 0..kw {
            let (name, h64) = w.name_pool.get_name_and_hash(id as u32);
            let global_id = global_name_pool.intern_with_hash(name, h64);
            trans.push(global_id);
        }
        *merge_intern_secs += t0.elapsed().as_secs_f64();

        let t1 = std::time::Instant::now();
        // Merge country data into global_aggs
        for (c_idx, c) in w.country_aggs.into_iter().enumerate() {
            let g = &mut global_aggs[c_idx];
            if c.count == 0 {
                continue;
            }
            if g.count == 0 {
                g.count = c.count;
                g.id_sum = c.id_sum;
                g.amount_sum = c.amount_sum;
                g.amount_min = c.amount_min;
                g.amount_max = c.amount_max;
                g.name_bytes = c.name_bytes;
                g.note_bytes = c.note_bytes;
            } else {
                g.count += c.count;
                g.id_sum += c.id_sum;
                g.amount_sum += c.amount_sum;
                if let Some(min_cents) = c.amount_min {
                    g.amount_min = Some(match g.amount_min {
                        Some(cur) => cur.min(min_cents),
                        None => min_cents,
                    });
                }
                if let Some(max_cents) = c.amount_max {
                    g.amount_max = Some(match g.amount_max {
                        Some(cur) => cur.max(max_cents),
                        None => max_cents,
                    });
                }
                g.name_bytes += c.name_bytes;
                g.note_bytes += c.note_bytes;
            }

            // Merge bitsets
            for (word_idx, &word) in c.seen_names.iter().enumerate() {
                let mut bit_word = word;
                while bit_word != 0 {
                    let bit = bit_word.trailing_zeros();
                    let local_id = (word_idx * 64 + bit as usize) as u32;
                    let global_id = trans[local_id as usize];
                    let g_word = (global_id / 64) as usize;
                    let g_mask = 1u64 << (global_id % 64);
                    if g_word >= g.seen_names.len() {
                        g.seen_names.resize(g_word + 1, 0);
                    }
                    g.seen_names[g_word] |= g_mask;
                    bit_word &= bit_word - 1;
                }
            }
        }
        *merge_bitset_secs += t1.elapsed().as_secs_f64();
    } else {
        let t1 = std::time::Instant::now();
        // w has no names, just merge scalar country data
        for (c_idx, c) in w.country_aggs.into_iter().enumerate() {
            let g = &mut global_aggs[c_idx];
            if c.count == 0 {
                continue;
            }
            if g.count == 0 {
                g.count = c.count;
                g.id_sum = c.id_sum;
                g.amount_sum = c.amount_sum;
                g.amount_min = c.amount_min;
                g.amount_max = c.amount_max;
                g.name_bytes = c.name_bytes;
                g.note_bytes = c.note_bytes;
            } else {
                g.count += c.count;
                g.id_sum += c.id_sum;
                g.amount_sum += c.amount_sum;
                if let Some(min_cents) = c.amount_min {
                    g.amount_min = Some(match g.amount_min {
                        Some(cur) => cur.min(min_cents),
                        None => min_cents,
                    });
                }
                if let Some(max_cents) = c.amount_max {
                    g.amount_max = Some(match g.amount_max {
                        Some(cur) => cur.max(max_cents),
                        None => max_cents,
                    });
                }
                g.name_bytes += c.name_bytes;
                g.note_bytes += c.note_bytes;
            }
        }
        *merge_bitset_secs += t1.elapsed().as_secs_f64();
    }
    let t_drop = std::time::Instant::now();
    drop(w.name_pool);
    *merge_dealloc_secs += t_drop.elapsed().as_secs_f64();
}

pub struct ExecutionStats {
    pub worker_count: usize,
    pub parse_time_secs: f64,
    pub merge_time_secs: f64,
    pub merge_intern_secs: f64,
    pub merge_bitset_secs: f64,
    pub merge_dealloc_secs: f64,
    pub chunk_sizes: Vec<usize>,
}

pub fn execute_join_workers_with_stats(
    records_data: &[u8],
    regions_data: &[u8],
    num_workers: usize,
) -> Result<(Vec<u8>, ExecutionStats), String> {
    let region_table = RegionTable::from_bytes(regions_data)?;
    let bounds = find_chunk_boundaries(records_data, num_workers);

    if bounds.len() < num_workers + 1 {
        // Fallback for small or empty inputs
        let out = execute_join_chunked(records_data, regions_data, 1)?;
        return Ok((
            out,
            ExecutionStats {
                worker_count: 1,
                parse_time_secs: 0.0,
                merge_time_secs: 0.0,
                merge_intern_secs: 0.0,
                merge_bitset_secs: 0.0,
                merge_dealloc_secs: 0.0,
                chunk_sizes: vec![records_data.len()],
            },
        ));
    }

    let chunks: Vec<&[u8]> = bounds.windows(2).map(|w| &records_data[w[0]..w[1]]).collect();
    let chunk_sizes: Vec<usize> = chunks.iter().map(|c| c.len()).collect();

    let t_parse_start = std::time::Instant::now();
    let results: Vec<Result<WorkerAccumulator, String>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_workers);
        for (i, &chunk) in chunks.iter().enumerate() {
            let is_first = i == 0;
            let rt = &region_table;
            handles.push(s.spawn(move || parse_chunk_worker(chunk, is_first, rt)));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut workers = Vec::with_capacity(num_workers);
    for r in results {
        workers.push(r?);
    }
    let parse_time = t_parse_start.elapsed().as_secs_f64();

    let t_merge_start = std::time::Instant::now();
    let mut iter = workers.into_iter();
    let first = iter.next().unwrap();
    let mut global_aggs = first.country_aggs;
    let mut global_name_pool = first.name_pool;

    let mut merge_intern_secs = 0.0;
    let mut merge_bitset_secs = 0.0;
    let mut merge_dealloc_secs = 0.0;

    for w in iter {
        merge_single_worker(
            &mut global_aggs,
            &mut global_name_pool,
            w,
            &mut merge_intern_secs,
            &mut merge_bitset_secs,
            &mut merge_dealloc_secs,
        );
    }

    // Filter countries with count > 0 and sort bytewise ascending
    let mut active_countries: Vec<&CountryAccumulator> = global_aggs.iter().filter(|c| c.count > 0).collect();
    active_countries.sort_by(|a, b| a.code.cmp(&b.code));

    let mut output = String::with_capacity(active_countries.len() * 80);
    for country in active_countries {
        country.format_line(&mut output);
    }
    let merge_time = t_merge_start.elapsed().as_secs_f64();

    Ok((
        output.into_bytes(),
        ExecutionStats {
            worker_count: num_workers,
            parse_time_secs: parse_time,
            merge_time_secs: merge_time,
            merge_intern_secs,
            merge_bitset_secs,
            merge_dealloc_secs,
            chunk_sizes,
        },
    ))
}

pub fn execute_join_2workers(records_data: &[u8], regions_data: &[u8]) -> Result<Vec<u8>, String> {
    let (out, _) = execute_join_workers_with_stats(records_data, regions_data, 2)?;
    Ok(out)
}

pub fn execute_join_4workers(records_data: &[u8], regions_data: &[u8]) -> Result<Vec<u8>, String> {
    let (out, _) = execute_join_workers_with_stats(records_data, regions_data, 4)?;
    Ok(out)
}

pub fn execute_join_8workers(records_data: &[u8], regions_data: &[u8]) -> Result<Vec<u8>, String> {
    let (out, _) = execute_join_workers_with_stats(records_data, regions_data, 8)?;
    Ok(out)
}

pub fn execute_join_chunked(records_data: &[u8], regions_data: &[u8], num_chunks: usize) -> Result<Vec<u8>, String> {
    let region_table = RegionTable::from_bytes(regions_data)?;
    let mut country_aggs: Vec<CountryAccumulator> = region_table
        .countries
        .iter()
        .map(|code| CountryAccumulator::new(code.clone()))
        .collect();

    let mut name_pool = NamePool::new();
    let bounds = find_chunk_boundaries(records_data, num_chunks);

    for (chunk_idx, window) in bounds.windows(2).enumerate() {
        let chunk_data = &records_data[window[0]..window[1]];
        if chunk_data.is_empty() {
            continue;
        }
        let is_first = chunk_idx == 0;
        let mut parser = RecordParser::new_with_header(chunk_data, is_first)?;

        parser.next_record(|id, name_slice, name_bytes, note_bytes, region_id, cents| {
            let country_idx = region_table.lookup(region_id);
            let name_id = name_pool.intern(name_slice);
            country_aggs[country_idx].add(id, name_id, name_bytes, note_bytes, cents);
            Ok(())
        })?;
    }

    let mut active_countries: Vec<&CountryAccumulator> = country_aggs.iter().filter(|c| c.count > 0).collect();
    active_countries.sort_by(|a, b| a.code.cmp(&b.code));

    let mut output = String::with_capacity(active_countries.len() * 80);
    for country in active_countries {
        country.format_line(&mut output);
    }

    Ok(output.into_bytes())
}

pub fn execute_join(records_data: &[u8], regions_data: &[u8]) -> Result<Vec<u8>, String> {
    let num_workers = std::env::var("SPEEDDEMON_WORKERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    let (out, _) = execute_join_workers_with_stats(records_data, regions_data, num_workers)?;
    Ok(out)
}

#[cfg(unix)]
pub struct ReadOnlyMappedFile {
    ptr: *const u8,
    len: usize,
    _file: fs::File,
}

#[cfg(unix)]
impl ReadOnlyMappedFile {
    pub fn open(path: &Path) -> Result<Self, String> {
        use std::os::unix::io::AsRawFd;
        let file = fs::File::open(path).map_err(|e| format!("cannot open {}: {}", path.display(), e))?;
        let len = file.metadata().map_err(|e| e.to_string())?.len() as usize;
        if len == 0 {
            return Ok(Self {
                ptr: std::ptr::null(),
                len: 0,
                _file: file,
            });
        }
        let fd = file.as_raw_fd();
        let ptr = unsafe {
            libc_mmap(
                std::ptr::null_mut(),
                len,
                PROT_READ,
                MAP_PRIVATE,
                fd,
                0,
            )
        };
        if ptr == MAP_FAILED {
            return Err(format!("mmap failed for {}", path.display()));
        }
        unsafe {
            libc_madvise(ptr, len, MADV_SEQUENTIAL);
        }
        Ok(Self {
            ptr: ptr as *const u8,
            len,
            _file: file,
        })
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[u8] {
        if self.len == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
        }
    }
}

#[cfg(unix)]
impl Drop for ReadOnlyMappedFile {
    fn drop(&mut self) {
        if !self.ptr.is_null() && self.len > 0 {
            unsafe {
                libc_munmap(self.ptr as *mut std::ffi::c_void, self.len);
            }
        }
    }
}

#[cfg(unix)]
const PROT_READ: i32 = 1;
#[cfg(unix)]
const MAP_PRIVATE: i32 = 2;
#[cfg(unix)]
const MAP_FAILED: *mut std::ffi::c_void = !0usize as *mut std::ffi::c_void;
#[cfg(unix)]
const MADV_SEQUENTIAL: i32 = 2;

#[cfg(unix)]
extern "C" {
    #[link_name = "mmap"]
    fn libc_mmap(
        addr: *mut std::ffi::c_void,
        len: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: i64,
    ) -> *mut std::ffi::c_void;

    #[link_name = "munmap"]
    fn libc_munmap(addr: *mut std::ffi::c_void, len: usize) -> i32;

    #[link_name = "madvise"]
    fn libc_madvise(addr: *mut std::ffi::c_void, len: usize, advice: i32) -> i32;
}

#[cfg(not(unix))]
pub struct ReadOnlyMappedFile {
    data: Vec<u8>,
}

#[cfg(not(unix))]
impl ReadOnlyMappedFile {
    pub fn open(path: &Path) -> Result<Self, String> {
        let data = fs::read(path).map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
        Ok(Self { data })
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[u8] {
        &self.data
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} <data_dir> <out_dir>", &args[0]);
        std::process::exit(1);
    }
    let data_dir = &args[1];
    let out_dir = &args[2];

    let regions_path = Path::new(data_dir).join("regions.csv");
    let records_path = Path::new(data_dir).join("records.csv");

    if !regions_path.exists() || !records_path.exists() {
        eprintln!(
            "Input files missing: {} or {}",
            regions_path.display(),
            records_path.display()
        );
        std::process::exit(1);
    }

    let regions_data = fs::read(&regions_path).expect("failed to read regions.csv");
    let records_file = ReadOnlyMappedFile::open(&records_path).expect("failed to map records.csv");
    let records_data = records_file.as_slice();

    let num_workers = std::env::var("SPEEDDEMON_WORKERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);

    let (output_bytes, stats) = execute_join_workers_with_stats(records_data, &regions_data, num_workers)
        .expect("join execution failed");

    let chunk_desc = stats
        .chunk_sizes
        .iter()
        .enumerate()
        .map(|(i, &sz)| format!("Chunk{}: {}B", i, sz))
        .collect::<Vec<_>>()
        .join(", ");

    eprintln!(
        "Workers: {}, {} | Parse: {:.4}s, Merge: {:.4}s (intern: {:.4}s, bitset: {:.4}s, dealloc: {:.4}s)",
        stats.worker_count, chunk_desc, stats.parse_time_secs, stats.merge_time_secs,
        stats.merge_intern_secs, stats.merge_bitset_secs, stats.merge_dealloc_secs
    );

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create output directory");
    let out_file_path = out_dir_path.join("aggregates.txt");

    let mut file = fs::File::create(&out_file_path).expect("failed to create aggregates.txt");
    file.write_all(&output_bytes).expect("failed to write output");

    #[cfg(target_os = "linux")]
    {
        let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
        for line in status.lines() {
            if line.starts_with("VmHWM:") || line.starts_with("RssAnon:") || line.starts_with("RssFile:") {
                eprintln!("{}", line.trim());
            }
        }
        if let Ok(cgroup_peak) = fs::read_to_string("/sys/fs/cgroup/memory.peak") {
            if let Ok(bytes) = cgroup_peak.trim().parse::<u64>() {
                eprintln!("cgroup_peak: {} kB", bytes / 1024);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const WORKED_RECORDS: &[u8] = b"\xEF\xBB\xBFid,name,note,region_id,amount\r\n\
1,\"Kaphar, Titus\",\"said \"\"no\"\" twice\",7,1420.00\r\n\
2,\"Betts\",\"a note that\nspans two lines\",7,88.50\n\
3,,\"\",12,0.00\r\n\
4,\"trailing space \",\"comma, quote \"\" and newline\ntogether\",3,-5.25\n\
\xEF\xBB\xBF5,\"Betts \",\"one\ntwo\nthree\",12,-0.75\r\n\
6,\"\",,12,10.00\r\n\
\xEF\xBB\xBF7,\"Ann \"\"Annie\"\" Lee\",\"x\",5,2.00\n\
8,\"Nobody\",\"\",4000000,-1.00\r\n\
9,\"Neg\",\"n\",20,-0.05\r\n";

    const WORKED_REGIONS: &[u8] = b"region_id,country\n3,BBB\n7,AAA\n12,AAA\n20,CCC\n21,DDD\n";

    const WORKED_OUTPUT: &[u8] = b"AAA 5 17 1517.75 -0.75 1420.00 4 24 55\n\
BBB 1 4 -5.25 -5.25 -5.25 1 15 35\n\
CCC 1 9 -0.05 -0.05 -0.05 1 3 1\n\
_UNMATCHED 2 15 1.00 -1.00 2.00 2 21 1\n";

    const RULES_RECORDS: &[u8] = b"id,name,note,region_id,amount\n\
1,\"a\xEF\xBB\xBFb\",\"x\n\xEF\xBB\xBFy\",7,1.00\n\
2,\"\xEF\xBB\xBF\",\"\",7,-1.00\r\n\
4,\"d\",\"\",8,5.00\n\
5,\"d \",\"\",8,-5.00\r\n\
\xEF\xBB\xBF3,\"c\",,7,0.50";

    const RULES_REGIONS: &[u8] = b"region_id,country\n7,AAA\n8,BBB\n";

    const RULES_OUTPUT: &[u8] = b"AAA 3 6 0.50 -1.00 1.00 3 9 6\n\
BBB 2 9 0.00 -5.00 5.00 2 3 0\n";

    #[test]
    fn test_format_cents() {
        assert_eq!(format_cents(-525), "-5.25");
        assert_eq!(format_cents(-5), "-0.05");
        assert_eq!(format_cents(0), "0.00");
        assert_eq!(format_cents(142000), "1420.00");
        assert_eq!(format_cents(5), "0.05");
        assert_eq!(format_cents(100), "1.00");
        assert_eq!(format_cents(-9223372036854775807), "-92233720368547758.07");
        assert_eq!(format_cents(i64::MIN), "-92233720368547758.08");
        assert_eq!(format_cents(i64::MAX), "92233720368547758.07");
    }

    #[test]
    fn test_worked_example_end_to_end() {
        let out = execute_join(WORKED_RECORDS, WORKED_REGIONS).unwrap();
        assert_eq!(out, WORKED_OUTPUT);
    }

    #[test]
    fn test_rules_example_end_to_end() {
        let out = execute_join(RULES_RECORDS, RULES_REGIONS).unwrap();
        assert_eq!(out, RULES_OUTPUT);
    }

    #[test]
    fn test_sorting_and_unmatched_position() {
        let records = b"id,name,note,region_id,amount\n\
1,\"A\",\"\",1,1.00\n\
2,\"B\",\"\",2,2.00\n\
3,\"C\",\"\",999,3.00\n\
4,\"D\",\"\",3,4.00\n";
        let regions = b"region_id,country\n1,ZZZ\n2,AAA\n3,MMM\n";
        let out = execute_join(records, regions).unwrap();
        let expected = b"AAA 1 2 2.00 2.00 2.00 1 1 0\n\
MMM 1 4 4.00 4.00 4.00 1 1 0\n\
ZZZ 1 1 1.00 1.00 1.00 1 1 0\n\
_UNMATCHED 1 3 3.00 3.00 3.00 1 1 0\n";
        assert_eq!(out, expected);
    }

    #[test]
    fn test_duplicate_names_within_country() {
        let mut pool = NamePool::new();
        let mut country = CountryAccumulator::new(b"AAA".to_vec());

        let id1 = pool.intern(b"Alice");
        let id2 = pool.intern(b"Alice");
        assert_eq!(id1, id2);
        assert_eq!(pool.len(), 1);

        country.add(1, id1, 5, 0, 100);
        country.add(2, id2, 5, 0, 200);

        assert_eq!(country.count, 2);
        assert_eq!(country.distinct_names_count(), 1);
    }

    #[test]
    fn test_same_name_different_countries() {
        let mut pool = NamePool::new();
        let mut country_a = CountryAccumulator::new(b"AAA".to_vec());
        let mut country_b = CountryAccumulator::new(b"BBB".to_vec());

        let id_a = pool.intern(b"Alice");
        let id_b = pool.intern(b"Alice");
        assert_eq!(id_a, id_b);
        assert_eq!(pool.len(), 1);

        country_a.add(1, id_a, 5, 0, 100);
        country_b.add(2, id_b, 5, 0, 200);

        assert_eq!(country_a.count, 1);
        assert_eq!(country_a.distinct_names_count(), 1);
        assert_eq!(country_b.count, 1);
        assert_eq!(country_b.distinct_names_count(), 1);
    }

    #[test]
    fn test_empty_and_trailing_space_names() {
        let mut pool = NamePool::new();
        let mut country = CountryAccumulator::new(b"AAA".to_vec());

        let id_empty1 = pool.intern(b"");
        let id_betts = pool.intern(b"Betts");
        let id_betts_space = pool.intern(b"Betts ");
        let id_empty2 = pool.intern(b"");

        assert_eq!(id_empty1, id_empty2);
        assert_ne!(id_betts, id_betts_space);
        assert_ne!(id_empty1, id_betts);
        assert_eq!(pool.len(), 3);

        country.add(1, id_empty1, 0, 0, 10);
        country.add(2, id_betts, 5, 0, 20);
        country.add(3, id_betts_space, 6, 0, 30);
        country.add(4, id_empty2, 0, 0, 40);

        assert_eq!(country.count, 4);
        assert_eq!(country.distinct_names_count(), 3);
    }

    #[test]
    fn test_unmatched_region_id() {
        let regions = b"region_id,country\n3,BBB\n7,AAA\n12,AAA\n20,CCC\n21,DDD\n";
        let table = RegionTable::from_bytes(regions).unwrap();
        assert_eq!(table.max_region_id, 21);

        let idx_7 = table.lookup(7);
        assert_eq!(table.countries[idx_7], b"AAA");

        let idx_3 = table.lookup(3);
        assert_eq!(table.countries[idx_3], b"BBB");

        let idx_5 = table.lookup(5);
        assert_eq!(idx_5, table.unmatched_idx);
        assert_eq!(table.countries[idx_5], b"_UNMATCHED");

        let idx_4m = table.lookup(4_000_000);
        assert_eq!(idx_4m, table.unmatched_idx);
        assert_eq!(table.countries[idx_4m], b"_UNMATCHED");
    }

    #[test]
    fn test_output_spacing_and_final_newline() {
        let records = b"id,name,note,region_id,amount\n1,\"Alice\",\"Note\",1,10.50\n";
        let regions = b"region_id,country\n1,USA\n";
        let out = execute_join(records, regions).unwrap();
        assert_eq!(out, b"USA 1 1 10.50 10.50 10.50 1 5 4\n");
        assert!(out.ends_with(b"\n"));
        assert!(!out.ends_with(b"\r\n"));
        let line = std::str::from_utf8(&out).unwrap();
        let parts: Vec<&str> = line.trim_end_matches('\n').split(' ').collect();
        assert_eq!(parts.len(), 9);
        assert_eq!(parts, vec!["USA", "1", "1", "10.50", "10.50", "10.50", "1", "5", "4"]);
    }

    #[test]
    fn test_region_lookup_bounds_and_sentinel() {
        let regions = b"region_id,country\n1,AAA\n999999,ZZZ\n";
        let table = RegionTable::from_bytes(regions).unwrap();

        let idx_0 = table.lookup(0);
        assert_eq!(idx_0, table.unmatched_idx);
        assert_eq!(table.countries[idx_0], b"_UNMATCHED");

        let idx_1 = table.lookup(1);
        assert_eq!(table.countries[idx_1], b"AAA");

        let idx_missing = table.lookup(500_000);
        assert_eq!(idx_missing, table.unmatched_idx);
        assert_eq!(table.countries[idx_missing], b"_UNMATCHED");

        let idx_max = table.lookup(999_999);
        assert_eq!(table.countries[idx_max], b"ZZZ");

        let idx_1m = table.lookup(1_000_000);
        assert_eq!(idx_1m, table.unmatched_idx);
        assert_eq!(table.countries[idx_1m], b"_UNMATCHED");

        let idx_huge = table.lookup(9_999_999);
        assert_eq!(idx_huge, table.unmatched_idx);
        assert_eq!(table.countries[idx_huge], b"_UNMATCHED");

        assert_eq!(UNMATCHED_SENTINEL_U8, 255);
    }

    #[test]
    fn test_partition_target_inside_quoted_field() {
        let data = b"id,name,note,region_id,amount\r\n1,\"Kaphar, Titus\",\"note\",7,10.00\r\n2,\"Betts\",\"note2\",7,20.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds.len(), 3);
        assert_eq!(bounds[0], 0);
        assert_eq!(&data[bounds[1]-2..bounds[1]], b"\r\n");
        assert_eq!(bounds[2], data.len());

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 30.00"));
    }

    #[test]
    fn test_partition_target_inside_escaped_quotes() {
        let data = b"id,name,note,region_id,amount\r\n1,\"Ann \"\"Annie\"\" Lee\",\"note\",7,10.00\r\n2,\"Betts\",\"n\",7,20.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds.len(), 3);
        assert_eq!(&data[bounds[1]-2..bounds[1]], b"\r\n");

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 30.00"));
    }

    #[test]
    fn test_partition_target_inside_multiline_note_with_bare_lf() {
        let data = b"id,name,note,region_id,amount\r\n1,\"Betts\",\"line1\nline2\nline3\",7,10.00\r\n2,\"Nobody\",\"\",7,20.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds.len(), 3);
        assert_eq!(&data[bounds[1]-2..bounds[1]], b"\r\n");
        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 30.00"));
    }

    #[test]
    fn test_partition_crlf_followed_by_bom() {
        let data = b"id,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n\xEF\xBB\xBF2,\"B\",\"\",7,2.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds.len(), 3);
        assert_eq!(&data[bounds[1]-2..bounds[1]], b"\r\n");
        assert_eq!(&data[bounds[1]..bounds[1]+3], BOM);

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 3.00"));
    }

    #[test]
    fn test_partition_lf_only_records_between_crlf() {
        let data = b"id,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n2,\"B\",\"\",7,2.00\n3,\"C\",\"\",7,3.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds.len(), 3);
        assert_eq!(&data[bounds[1]-2..bounds[1]], b"\r\n");

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 3 6 6.00"));
    }

    #[test]
    fn test_partition_multiple_targets_resolving_to_same_boundary() {
        let data = b"id,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n2,\"B\",\"\",7,2.00\r\n";
        let bounds = find_chunk_boundaries(data, 12);
        for i in 0..bounds.len() - 1 {
            assert!(bounds[i] < bounds[i+1]);
        }
        assert_eq!(bounds[0], 0);
        assert_eq!(*bounds.last().unwrap(), data.len());

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 12).unwrap();
        assert!(out.starts_with(b"AAA 2 3 3.00"));
    }

    #[test]
    fn test_partition_target_inside_crlf_sequence() {
        let data = b"id,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n2,\"B\",\"\",7,2.00\r\n";
        let crlf_pos = data.windows(2).position(|w| w == b"\r\n").unwrap();
        let second_crlf_pos = crlf_pos + 2 + data[crlf_pos+2..].windows(2).position(|w| w == b"\r\n").unwrap();

        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds[1], second_crlf_pos + 2);

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 3.00"));
    }

    #[test]
    fn test_partition_empty_fields() {
        let data = b"id,name,note,region_id,amount\r\n1,\"\",\"\",7,0.00\r\n2,,\"\",7,0.00\r\n";
        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 0.00"));
    }

    #[test]
    fn test_partition_final_record_without_trailing_terminator() {
        let data = b"id,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n2,\"B\",\"\",7,2.00";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(*bounds.last().unwrap(), data.len());

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 2 3 3.00"));
    }

    #[test]
    fn test_partition_file_beginning_with_bom() {
        let data = b"\xEF\xBB\xBFid,name,note,region_id,amount\r\n1,\"A\",\"\",7,1.00\r\n";
        let bounds = find_chunk_boundaries(data, 2);
        assert_eq!(bounds[0], 0);

        let out = execute_join_chunked(data, b"region_id,country\n7,AAA\n", 2).unwrap();
        assert!(out.starts_with(b"AAA 1 1 1.00"));
    }

    #[test]
    fn test_partition_long_sequence_of_lf_records() {
        let mut data = Vec::from(b"id,name,note,region_id,amount\r\n".as_slice());
        for i in 1..=50 {
            let row = format!("{},\"Person_{}\",\"note\",7,1.00\n", i, i);
            data.extend_from_slice(row.as_bytes());
        }
        data.extend_from_slice(b"51,\"Last\",\"\",7,5.00\r\n");

        let bounds = find_chunk_boundaries(&data, 4);
        for i in 0..bounds.len() - 1 {
            assert!(bounds[i] < bounds[i+1]);
        }

        let out = execute_join_chunked(&data, b"region_id,country\n7,AAA\n", 4).unwrap();
        assert!(out.starts_with(b"AAA 51 1326 55.00"));
    }

    #[test]
    fn test_2workers_duplicate_names_both_workers() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"Alice\",\"n1\",7,10.00\r\n\
2,\"Alice\",\"n2\",7,20.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_2workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 2 3 30.00 10.00 20.00 1 10 4\n"));
    }

    #[test]
    fn test_2workers_same_name_multiple_countries() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"SharedName\",\"n1\",7,10.00\r\n\
2,\"SharedName\",\"n2\",8,20.00\r\n";
        let regions = b"region_id,country\n7,USA\n8,CAN\n";
        let out = execute_join_2workers(records, regions).unwrap();
        let out_str = std::str::from_utf8(&out).unwrap();
        assert!(out_str.contains("CAN 1 2 20.00 20.00 20.00 1 10 2\n"));
        assert!(out_str.contains("USA 1 1 10.00 10.00 10.00 1 10 2\n"));
    }

    #[test]
    fn test_2workers_empty_names() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"\",\"n1\",7,10.00\r\n\
2,,\"n2\",7,20.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_2workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 2 3 30.00 10.00 20.00 1 0 4\n"));
    }

    #[test]
    fn test_2workers_merge_ordering_and_deterministic_output() {
        let out_2w = execute_join_2workers(WORKED_RECORDS, WORKED_REGIONS).unwrap();
        let out_seq = execute_join_chunked(WORKED_RECORDS, WORKED_REGIONS, 1).unwrap();
        assert_eq!(out_2w, out_seq);
        assert_eq!(out_2w, WORKED_OUTPUT);
    }

    #[test]
    fn test_4workers_name_shared_across_all_four_workers() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"CommonPerson\",\"n1\",7,10.00\r\n\
2,\"CommonPerson\",\"n2\",7,20.00\r\n\
3,\"CommonPerson\",\"n3\",7,30.00\r\n\
4,\"CommonPerson\",\"n4\",7,40.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_4workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 4 10 100.00 10.00 40.00 1 48 8\n"));
    }

    #[test]
    fn test_4workers_names_shared_across_multiple_countries() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"Alice\",\"n1\",7,10.00\r\n\
2,\"Alice\",\"n2\",8,20.00\r\n\
3,\"Bob\",\"n3\",7,30.00\r\n\
4,\"Bob\",\"n4\",8,40.00\r\n";
        let regions = b"region_id,country\n7,USA\n8,CAN\n";
        let out = execute_join_4workers(records, regions).unwrap();
        let out_str = std::str::from_utf8(&out).unwrap();
        assert!(out_str.contains("CAN 2 6 60.00 20.00 40.00 2 8 4\n"));
        assert!(out_str.contains("USA 2 4 40.00 10.00 30.00 2 8 4\n"));
    }

    #[test]
    fn test_4workers_empty_names() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"\",\"n1\",7,10.00\r\n\
2,,\"n2\",7,20.00\r\n\
3,\"\",\"n3\",7,30.00\r\n\
4,,\"n4\",7,40.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_4workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 4 10 100.00 10.00 40.00 1 0 8\n"));
    }

    #[test]
    fn test_4workers_deterministic_merge_ordering() {
        let expected = execute_join_chunked(WORKED_RECORDS, WORKED_REGIONS, 1).unwrap();
        for _ in 0..5 {
            let out = execute_join_4workers(WORKED_RECORDS, WORKED_REGIONS).unwrap();
            assert_eq!(out, expected);
        }
    }

    #[test]
    fn test_8workers_name_shared_across_all_eight_workers() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"CommonPerson8\",\"n1\",7,10.00\r\n\
2,\"CommonPerson8\",\"n2\",7,20.00\r\n\
3,\"CommonPerson8\",\"n3\",7,30.00\r\n\
4,\"CommonPerson8\",\"n4\",7,40.00\r\n\
5,\"CommonPerson8\",\"n5\",7,50.00\r\n\
6,\"CommonPerson8\",\"n6\",7,60.00\r\n\
7,\"CommonPerson8\",\"n7\",7,70.00\r\n\
8,\"CommonPerson8\",\"n8\",7,80.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_8workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 8 36 360.00 10.00 80.00 1 104 16\n"));
    }

    #[test]
    fn test_8workers_names_shared_across_countries() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"Alice\",\"n1\",7,10.00\r\n\
2,\"Alice\",\"n2\",8,20.00\r\n\
3,\"Bob\",\"n3\",7,30.00\r\n\
4,\"Bob\",\"n4\",8,40.00\r\n\
5,\"Alice\",\"n5\",7,50.00\r\n\
6,\"Alice\",\"n6\",8,60.00\r\n\
7,\"Bob\",\"n7\",7,70.00\r\n\
8,\"Bob\",\"n8\",8,80.00\r\n";
        let regions = b"region_id,country\n7,USA\n8,CAN\n";
        let out = execute_join_8workers(records, regions).unwrap();
        let out_str = std::str::from_utf8(&out).unwrap();
        assert!(out_str.contains("CAN 4 20 200.00 20.00 80.00 2 16 8\n"));
        assert!(out_str.contains("USA 4 16 160.00 10.00 70.00 2 16 8\n"));
    }

    #[test]
    fn test_8workers_empty_names() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"\",\"n1\",7,10.00\r\n\
2,,\"n2\",7,20.00\r\n\
3,\"\",\"n3\",7,30.00\r\n\
4,,\"n4\",7,40.00\r\n\
5,\"\",\"n5\",7,50.00\r\n\
6,,\"n6\",7,60.00\r\n\
7,\"\",\"n7\",7,70.00\r\n\
8,,\"n8\",7,80.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_8workers(records, regions).unwrap();
        assert!(out.starts_with(b"USA 8 36 360.00 10.00 80.00 1 0 16\n"));
    }

    #[test]
    fn test_8workers_unmatched_regions() {
        let records = b"id,name,note,region_id,amount\r\n\
1,\"A\",\"n1\",7,10.00\r\n\
2,\"B\",\"n2\",9999999,20.00\r\n\
3,\"C\",\"n3\",7,30.00\r\n\
4,\"D\",\"n4\",0,40.00\r\n\
5,\"E\",\"n5\",7,50.00\r\n\
6,\"F\",\"n6\",1000000,60.00\r\n\
7,\"G\",\"n7\",7,70.00\r\n\
8,\"H\",\"n8\",500000,80.00\r\n";
        let regions = b"region_id,country\n7,USA\n";
        let out = execute_join_8workers(records, regions).unwrap();
        let out_str = std::str::from_utf8(&out).unwrap();
        assert!(out_str.contains("USA 4 16 160.00 10.00 70.00 4 4 8\n"));
        assert!(out_str.contains("_UNMATCHED 4 20 200.00 20.00 80.00 4 4 8\n"));
    }

    #[test]
    fn test_8workers_deterministic_merge_ordering() {
        let expected = execute_join_chunked(WORKED_RECORDS, WORKED_REGIONS, 1).unwrap();
        for _ in 0..5 {
            let out = execute_join_8workers(WORKED_RECORDS, WORKED_REGIONS).unwrap();
            assert_eq!(out, expected);
        }
    }

    // --- Phase 4F Stage 2 & 3 Arena and Pre-Hashing Tests ---

    #[test]
    fn test_empty_names_and_duplicates() {
        let mut pool = NamePool::new();
        let id0 = pool.intern(b"");
        let id1 = pool.intern(b"");
        assert_eq!(id0, 0);
        assert_eq!(id1, 0);
        assert_eq!(pool.len(), 1);
        assert_eq!(pool.get_name(0), b"");

        let id_other = pool.intern(b"Not empty");
        assert_eq!(id_other, 1);
        assert_eq!(pool.intern(b""), 0);
        assert_eq!(pool.get_name(0), b"");
        assert_eq!(pool.get_name(1), b"Not empty");
    }

    #[test]
    fn test_deliberate_full_hash_collisions() {
        let mut pool = NamePool::new();
        let synthetic_hash: u64 = 0xabcdef0123456789;
        let s1 = b"deliberate_collision_string_alpha";
        let s2 = b"deliberate_collision_string_beta";

        // Intern two distinct strings with identical 64-bit full hash
        let id1 = pool.intern_with_hash(s1, synthetic_hash);
        let id2 = pool.intern_with_hash(s2, synthetic_hash);

        // They must receive different IDs
        assert_ne!(id1, id2);
        assert_eq!(pool.len(), 2);

        // Both strings must be faithfully preserved and retrievable
        assert_eq!(pool.get_name(id1), s1.as_slice());
        assert_eq!(pool.get_name(id2), s2.as_slice());

        let (ret_s1, ret_h1) = pool.get_name_and_hash(id1);
        assert_eq!(ret_s1, s1.as_slice());
        assert_eq!(ret_h1, synthetic_hash);

        let (ret_s2, ret_h2) = pool.get_name_and_hash(id2);
        assert_eq!(ret_s2, s2.as_slice());
        assert_eq!(ret_h2, synthetic_hash);

        // Re-interning with identical hash must resolve each correctly without cross-match
        assert_eq!(pool.intern_with_hash(s1, synthetic_hash), id1);
        assert_eq!(pool.intern_with_hash(s2, synthetic_hash), id2);
    }

    #[test]
    fn test_different_names_with_matching_hash_tags() {
        let mut pool = NamePool::new();
        // Construct two hashes with different h64 but identical 32-bit hash_tag
        // tag = (h ^ (h >> 32)) as u32
        let h1: u64 = 0x0000000100000002; // tag = 1 ^ 2 = 3
        let h2: u64 = 0x0000000200000001; // tag = 2 ^ 1 = 3
        assert_eq!(hash_tag_from_u64(h1), hash_tag_from_u64(h2));
        assert_ne!(h1, h2);

        let s1 = b"string_for_h1";
        let s2 = b"string_for_h2_same_len";

        let id1 = pool.intern_with_hash(s1, h1);
        let id2 = pool.intern_with_hash(s2, h2);
        assert_ne!(id1, id2);

        assert_eq!(pool.get_name(id1), s1.as_slice());
        assert_eq!(pool.get_name(id2), s2.as_slice());
    }

    #[test]
    fn test_arena_growth_and_table_resizing() {
        let mut pool = NamePool::new();
        let initial_cap = pool.capacity();
        let num_entries = 5000;

        for i in 0..num_entries {
            let name = format!("entry_{:06}", i);
            let id = pool.intern(name.as_bytes());
            assert_eq!(id, i as u32);
        }

        assert_eq!(pool.len(), num_entries);
        assert!(pool.capacity() > initial_cap);

        for i in 0..num_entries {
            let name = format!("entry_{:06}", i);
            let id = pool.intern(name.as_bytes());
            assert_eq!(id, i as u32);
            assert_eq!(pool.get_name(id), name.as_bytes());
        }
    }

    #[test]
    fn test_offset_stability_after_repeated_arena_growth() {
        let mut pool = NamePool::new();
        let mut initial_names = Vec::new();
        let mut initial_ids = Vec::new();

        for i in 0..100 {
            let s = format!("prefix_{}_with_some_long_padding_bytes_{}", i, "x".repeat(i * 3));
            let bytes = s.into_bytes();
            let id = pool.intern(&bytes);
            initial_ids.push(id);
            initial_names.push(bytes);
        }

        for i in 100..10000 {
            let name = format!("more_names_{}", i);
            pool.intern(name.as_bytes());
        }

        for (idx, &id) in initial_ids.iter().enumerate() {
            let (name_slice, h) = pool.get_name_and_hash(id);
            assert_eq!(name_slice, initial_names[idx].as_slice());
            assert_eq!(h, hash_name_u64(&initial_names[idx]));
        }
    }
}
