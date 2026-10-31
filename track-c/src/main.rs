use std::env;
use std::fs;
use std::path::Path;

const BOM: &[u8] = b"\xEF\xBB\xBF";
const UNMATCHED_COUNTRY_IDX: usize = 240;

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

pub fn format_cents(cents: i64) -> String {
    let mut out = String::with_capacity(16);
    if cents < 0 {
        out.push('-');
    }
    let abs_val: u64 = cents.unsigned_abs();
    let dollars = abs_val / 100;
    let rem = abs_val % 100;
    use std::fmt::Write;
    let _ = write!(out, "{}.{:02}", dollars, rem);
    out
}

struct RegionLookup {
    region_to_country: Vec<u8>,
    countries: Vec<[u8; 3]>,
}

impl RegionLookup {
    fn parse(data: &[u8]) -> Self {
        let mut country_seen = [false; 26 * 26 * 26];
        let mut country_names: Vec<[u8; 3]> = Vec::with_capacity(256);

        let mut pos = 0;
        while pos < data.len() && data[pos] != b'\n' {
            pos += 1;
        }
        if pos < data.len() && data[pos] == b'\n' {
            pos += 1;
        }
        let body_start = pos;

        // Pass 1: find unique countries and max_region
        let mut max_region = 0usize;
        while pos < data.len() {
            let mut rid = 0usize;
            while pos < data.len() && data[pos] != b',' {
                let b = data[pos];
                if b >= b'0' && b <= b'9' {
                    rid = rid * 10 + (b - b'0') as usize;
                }
                pos += 1;
            }
            if pos < data.len() && data[pos] == b',' {
                pos += 1;
            }
            if rid > max_region {
                max_region = rid;
            }

            if pos + 3 <= data.len() && data[pos] >= b'A' && data[pos] <= b'Z' && data[pos + 1] >= b'A' && data[pos + 1] <= b'Z' && data[pos + 2] >= b'A' && data[pos + 2] <= b'Z' {
                let c0 = (data[pos] - b'A') as usize;
                let c1 = (data[pos + 1] - b'A') as usize;
                let c2 = (data[pos + 2] - b'A') as usize;
                let code_idx = c0 * 676 + c1 * 26 + c2;
                if code_idx < country_seen.len() && !country_seen[code_idx] {
                    country_seen[code_idx] = true;
                    country_names.push([data[pos], data[pos + 1], data[pos + 2]]);
                }
            }
            while pos < data.len() && data[pos] != b'\n' {
                pos += 1;
            }
            if pos < data.len() && data[pos] == b'\n' {
                pos += 1;
            }
        }

        country_names.sort_unstable();
        let mut code_to_country = [UNMATCHED_COUNTRY_IDX as u8; 26 * 26 * 26];
        for (i, code) in country_names.iter().enumerate() {
            let c0 = (code[0] - b'A') as usize;
            let c1 = (code[1] - b'A') as usize;
            let c2 = (code[2] - b'A') as usize;
            code_to_country[c0 * 676 + c1 * 26 + c2] = i as u8;
        }

        // Pass 2: populate region_to_country
        let mut region_to_country = vec![UNMATCHED_COUNTRY_IDX as u8; max_region + 1];
        pos = body_start;
        while pos < data.len() {
            let mut rid = 0usize;
            while pos < data.len() && data[pos] != b',' {
                let b = data[pos];
                if b >= b'0' && b <= b'9' {
                    rid = rid * 10 + (b - b'0') as usize;
                }
                pos += 1;
            }
            if pos < data.len() && data[pos] == b',' {
                pos += 1;
            }

            if pos + 3 <= data.len() && data[pos] >= b'A' && data[pos] <= b'Z' && data[pos + 1] >= b'A' && data[pos + 1] <= b'Z' && data[pos + 2] >= b'A' && data[pos + 2] <= b'Z' {
                let c0 = (data[pos] - b'A') as usize;
                let c1 = (data[pos + 1] - b'A') as usize;
                let c2 = (data[pos + 2] - b'A') as usize;
                let code_idx = c0 * 676 + c1 * 26 + c2;
                if code_idx < code_to_country.len() {
                    region_to_country[rid] = code_to_country[code_idx];
                }
            }
            while pos < data.len() && data[pos] != b'\n' {
                pos += 1;
            }
            if pos < data.len() && data[pos] == b'\n' {
                pos += 1;
            }
        }

        Self {
            region_to_country,
            countries: country_names,
        }
    }

    #[inline(always)]
    fn get_country(&self, rid: usize) -> usize {
        if rid < self.region_to_country.len() {
            self.region_to_country[rid] as usize
        } else {
            UNMATCHED_COUNTRY_IDX
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
pub fn hash_tag_from_u64(h: u64) -> u32 {
    (h ^ (h >> 32)) as u32
}

pub struct NamePool {
    slots: Vec<NameSlot>,
    arena: Vec<u8>,
    entries: Vec<NameEntry>,
    count: usize,
    mask: usize,
}

impl NamePool {
    pub fn new(capacity: usize) -> Self {
        let cap = capacity.next_power_of_two().max(1024);
        Self {
            slots: vec![NameSlot::default(); cap],
            arena: Vec::with_capacity(64 * 1024),
            entries: Vec::with_capacity(1024),
            count: 0,
            mask: cap - 1,
        }
    }

    #[inline(always)]
    pub fn intern(&mut self, name: &[u8], h64: u64) -> u32 {
        let tag = hash_tag_from_u64(h64);
        let mut idx = (h64 as usize) & self.mask;

        loop {
            let slot = self.slots[idx];
            if slot.name_id == NAME_EMPTY_SENTINEL {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern(name, h64);
                }

                let offset = self.arena.len() as u32;
                let len = name.len() as u32;
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
        let mut new_slots = vec![NameSlot::default(); new_cap];

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

    #[inline(always)]
    pub fn get_name(&self, id: u32) -> (&[u8], u64) {
        let entry = self.entries[id as usize];
        let start = entry.offset as usize;
        let end = start + entry.len as usize;
        (&self.arena[start..end], entry.hash)
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }
}

#[derive(Clone, Default)]
struct CountryAgg {
    count: usize,
    id_sum: u64,
    amount_sum: i64,
    amount_min: i64,
    amount_max: i64,
    name_bytes: u64,
    note_bytes: u64,
    seen_names: Vec<u64>,
}

impl CountryAgg {
    #[inline(always)]
    fn mark_name(&mut self, name_id: u32) {
        let word_idx = (name_id / 64) as usize;
        let bit_mask = 1u64 << (name_id % 64);
        if word_idx >= self.seen_names.len() {
            self.seen_names.resize(word_idx + 1, 0);
        }
        self.seen_names[word_idx] |= bit_mask;
    }
}

struct WorkerState {
    aggs: Vec<CountryAgg>,
    pool: NamePool,
}

fn parse_records_chunk(
    data: &[u8],
    lookup: &RegionLookup,
) -> WorkerState {
    let mut aggs = vec![CountryAgg {
        amount_min: i64::MAX,
        amount_max: i64::MIN,
        ..Default::default()
    }; UNMATCHED_COUNTRY_IDX + 1];

    let mut pool = NamePool::new(2048);
    let mut pos = 0;
    let end = data.len();
    let mut scratch = Vec::with_capacity(256);

    while pos < end {
        if pos + 2 < end && &data[pos..pos + 3] == BOM {
            pos += 3;
        }
        if pos >= end {
            break;
        }

        // Col 0: id
        let mut id_val = 0u64;
        while pos < end && data[pos] != b',' {
            let b = data[pos];
            if b >= b'0' && b <= b'9' {
                id_val = id_val * 10 + (b - b'0') as u64;
            }
            pos += 1;
        }
        if pos < end && data[pos] == b',' {
            pos += 1;
        }

        // Col 1: name
        let (name_len, name_id) = if pos < end && data[pos] == b',' {
            pos += 1;
            let nid = pool.intern(b"", hash_name_u64(b""));
            (0u64, nid)
        } else if pos < end && data[pos] == b'"' {
            pos += 1;
            let mut unescaped_len = 0usize;
            let mut has_escapes = false;
            let start_name = pos;
            while pos < end {
                let b = data[pos];
                if b == b'"' {
                    if pos + 1 < end && data[pos + 1] == b'"' {
                        has_escapes = true;
                        unescaped_len += 1;
                        pos += 2;
                    } else {
                        pos += 1;
                        break;
                    }
                } else {
                    unescaped_len += 1;
                    pos += 1;
                }
            }
            let nid = if has_escapes {
                scratch.clear();
                scratch.reserve(unescaped_len);
                let mut i = start_name;
                while i < pos - 1 {
                    if data[i] == b'"' && data[i + 1] == b'"' {
                        scratch.push(b'"');
                        i += 2;
                    } else {
                        scratch.push(data[i]);
                        i += 1;
                    }
                }
                let h = hash_name_u64(&scratch);
                pool.intern(&scratch, h)
            } else {
                let slice = &data[start_name..pos - 1];
                let h = hash_name_u64(slice);
                pool.intern(slice, h)
            };
            if pos < end && data[pos] == b',' {
                pos += 1;
            }
            (unescaped_len as u64, nid)
        } else {
            let start_name = pos;
            while pos < end && data[pos] != b',' {
                pos += 1;
            }
            let raw = &data[start_name..pos];
            let h = hash_name_u64(raw);
            let nid = pool.intern(raw, h);
            let len = raw.len() as u64;
            if pos < end && data[pos] == b',' {
                pos += 1;
            }
            (len, nid)
        };

        // Col 2: note
        let note_len: u64 = if pos < end && data[pos] == b',' {
            pos += 1;
            0
        } else if pos < end && data[pos] == b'"' {
            pos += 1;
            let mut unescaped_len = 0usize;
            while pos < end {
                let b = data[pos];
                if b == b'"' {
                    if pos + 1 < end && data[pos + 1] == b'"' {
                        unescaped_len += 1;
                        pos += 2;
                    } else {
                        pos += 1;
                        break;
                    }
                } else {
                    unescaped_len += 1;
                    pos += 1;
                }
            }
            if pos < end && data[pos] == b',' {
                pos += 1;
            }
            unescaped_len as u64
        } else {
            let start_note = pos;
            while pos < end && data[pos] != b',' {
                pos += 1;
            }
            let len = (pos - start_note) as u64;
            if pos < end && data[pos] == b',' {
                pos += 1;
            }
            len
        };

        // Col 3: region_id
        let mut region_val = 0usize;
        while pos < end && data[pos] != b',' {
            let b = data[pos];
            if b >= b'0' && b <= b'9' {
                region_val = region_val * 10 + (b - b'0') as usize;
            }
            pos += 1;
        }
        if pos < end && data[pos] == b',' {
            pos += 1;
        }

        // Col 4: amount
        let mut neg = false;
        if pos < end && data[pos] == b'-' {
            neg = true;
            pos += 1;
        }
        let mut dollars = 0i64;
        while pos < end && data[pos] != b'.' && data[pos] != b'\r' && data[pos] != b'\n' {
            let b = data[pos];
            if b >= b'0' && b <= b'9' {
                dollars = dollars * 10 + (b - b'0') as i64;
            }
            pos += 1;
        }
        let mut cents = dollars * 100;
        if pos < end && data[pos] == b'.' {
            pos += 1;
            if pos < end && data[pos] >= b'0' && data[pos] <= b'9' {
                cents += ((data[pos] - b'0') as i64) * 10;
                pos += 1;
            }
            if pos < end && data[pos] >= b'0' && data[pos] <= b'9' {
                cents += (data[pos] - b'0') as i64;
                pos += 1;
            }
        }
        let amount_cents = if neg { -cents } else { cents };

        while pos < end && data[pos] != b'\n' {
            pos += 1;
        }
        if pos < end && data[pos] == b'\n' {
            pos += 1;
        }

        let country_idx = lookup.get_country(region_val);
        let agg = &mut aggs[country_idx];
        agg.count += 1;
        agg.id_sum += id_val;
        agg.amount_sum += amount_cents;
        if amount_cents < agg.amount_min {
            agg.amount_min = amount_cents;
        }
        if amount_cents > agg.amount_max {
            agg.amount_max = amount_cents;
        }
        agg.name_bytes += name_len;
        agg.note_bytes += note_len;
        agg.mark_name(name_id);
    }

    WorkerState { aggs, pool }
}

fn find_chunk_boundaries(data: &[u8], num_chunks: usize) -> Vec<usize> {
    if num_chunks <= 1 || data.is_empty() {
        return vec![0, data.len()];
    }
    let chunk_size = data.len() / num_chunks;
    let mut boundaries = Vec::with_capacity(num_chunks + 1);
    boundaries.push(0);

    for i in 1..num_chunks {
        let nominal = i * chunk_size;
        let mut found = None;
        if nominal < data.len() {
            let mut j = nominal;
            while j + 1 < data.len() {
                if data[j] == b'\r' && data[j + 1] == b'\n' {
                    found = Some(j + 2);
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

#[cfg(unix)]
const PROT_READ: i32 = 1;
#[cfg(unix)]
const MAP_SHARED: i32 = 1;
#[cfg(unix)]
const MADV_SEQUENTIAL: i32 = 2;

#[cfg(unix)]
extern "C" {
    fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut std::ffi::c_void;
    fn munmap(addr: *mut std::ffi::c_void, len: usize) -> i32;
    fn madvise(addr: *mut std::ffi::c_void, len: usize, advice: i32) -> i32;
}

pub struct MmapFile {
    ptr: *mut std::ffi::c_void,
    len: usize,
    #[cfg(not(unix))]
    _data: Vec<u8>,
}

impl MmapFile {
    pub fn open(path: &Path) -> Result<Self, String> {
        #[cfg(unix)]
        {
            use std::os::unix::io::AsRawFd;
            let file = fs::File::open(path).map_err(|e| e.to_string())?;
            let meta = file.metadata().map_err(|e| e.to_string())?;
            let len = meta.len() as usize;
            if len == 0 {
                return Ok(Self { ptr: std::ptr::null_mut(), len: 0 });
            }
            let ptr = unsafe {
                mmap(std::ptr::null_mut(), len, PROT_READ, MAP_SHARED, file.as_raw_fd(), 0)
            };
            if ptr as isize == -1 {
                return Err("mmap failed".to_string());
            }
            unsafe {
                madvise(ptr, len, MADV_SEQUENTIAL);
            }
            Ok(Self { ptr, len })
        }
        #[cfg(not(unix))]
        {
            let _data = fs::read(path).map_err(|e| e.to_string())?;
            let len = _data.len();
            let ptr = _data.as_ptr() as *mut std::ffi::c_void;
            Ok(Self { ptr, len, _data })
        }
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[u8] {
        if self.len == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.ptr as *const u8, self.len) }
        }
    }
}

impl Drop for MmapFile {
    fn drop(&mut self) {
        #[cfg(unix)]
        {
            if self.len > 0 && !self.ptr.is_null() && self.ptr as isize != -1 {
                unsafe { munmap(self.ptr, self.len) };
            }
        }
    }
}

unsafe impl Send for MmapFile {}
unsafe impl Sync for MmapFile {}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let records_path = Path::new(data_dir).join("records.csv");
    let regions_path = Path::new(data_dir).join("regions.csv");

    if !records_path.exists() || !regions_path.exists() {
        eprintln!("Missing input files in {}", data_dir);
        std::process::exit(1);
    }

    let t0 = std::time::Instant::now();
    let regions_data = fs::read(&regions_path).expect("failed to read regions.csv");
    let lookup = RegionLookup::parse(&regions_data);
    let t_regions = t0.elapsed();

    let records_mmap = MmapFile::open(&records_path).expect("failed to mmap records.csv");
    let records_data = records_mmap.as_slice();

    let mut start_pos = 0;
    if records_data.starts_with(BOM) {
        start_pos += 3;
    }
    while start_pos < records_data.len() && records_data[start_pos] != b'\n' {
        start_pos += 1;
    }
    if start_pos < records_data.len() && records_data[start_pos] == b'\n' {
        start_pos += 1;
    }

    let payload = &records_data[start_pos..];

    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get().min(8))
                .unwrap_or(8)
        });

    let boundaries = find_chunk_boundaries(payload, num_threads.max(1));
    let num_chunks = boundaries.len() - 1;

    let t_parse_0 = std::time::Instant::now();
    let mut chunk_results: Vec<WorkerState> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_chunks);
        for i in 0..num_chunks {
            let start = boundaries[i];
            let end = boundaries[i + 1];
            let chunk_data = &payload[start..end];
            let l_ref = &lookup;
            handles.push(s.spawn(move || {
                parse_records_chunk(chunk_data, l_ref)
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let t_parse = t_parse_0.elapsed();

    let t_merge_0 = std::time::Instant::now();
    // Merge into worker 0
    let mut base_state = chunk_results.swap_remove(0);
    let mut remap_buf = Vec::with_capacity(32 * 1024);

    while !chunk_results.is_empty() {
        let other_worker = chunk_results.pop().unwrap();
        remap_buf.clear();
        let other_count = other_worker.pool.len();
        for i in 0..other_count {
            let (name, h) = other_worker.pool.get_name(i as u32);
            let global_id = base_state.pool.intern(name, h);
            remap_buf.push(global_id);
        }

        for c in 0..=UNMATCHED_COUNTRY_IDX {
            let other_agg = &other_worker.aggs[c];
            if other_agg.count == 0 {
                continue;
            }
            let base_agg = &mut base_state.aggs[c];
            base_agg.count += other_agg.count;
            base_agg.id_sum += other_agg.id_sum;
            base_agg.amount_sum += other_agg.amount_sum;
            base_agg.amount_min = base_agg.amount_min.min(other_agg.amount_min);
            base_agg.amount_max = base_agg.amount_max.max(other_agg.amount_max);
            base_agg.name_bytes += other_agg.name_bytes;
            base_agg.note_bytes += other_agg.note_bytes;

            for (w_idx, &word) in other_agg.seen_names.iter().enumerate() {
                if word == 0 {
                    continue;
                }
                let mut bits = word;
                let base_bit = (w_idx * 64) as u32;
                while bits != 0 {
                    let trailing = bits.trailing_zeros();
                    let local_id = (base_bit + trailing) as usize;
                    if local_id < remap_buf.len() {
                        let global_id = remap_buf[local_id];
                        base_agg.mark_name(global_id);
                    }
                    bits &= bits - 1;
                }
            }
        }
    }

    let t_merge = t_merge_0.elapsed();

    let t_out_0 = std::time::Instant::now();
    // Format output
    let mut out_buf = String::with_capacity(32 * 1024);
    for (i, code) in lookup.countries.iter().enumerate() {
        let agg = &base_state.aggs[i];
        if agg.count == 0 {
            continue;
        }
        let distinct: u64 = agg.seen_names.iter().map(|&w| w.count_ones() as u64).sum();
        let country_str = unsafe { std::str::from_utf8_unchecked(code) };
        let min_str = format_cents(agg.amount_min);
        let max_str = format_cents(agg.amount_max);
        let sum_str = format_cents(agg.amount_sum);

        use std::fmt::Write;
        let _ = writeln!(
            out_buf,
            "{} {} {} {} {} {} {} {} {}",
            country_str,
            agg.count,
            agg.id_sum,
            sum_str,
            min_str,
            max_str,
            distinct,
            agg.name_bytes,
            agg.note_bytes
        );
    }

    let agg = &base_state.aggs[UNMATCHED_COUNTRY_IDX];
    if agg.count > 0 {
        let distinct: u64 = agg.seen_names.iter().map(|&w| w.count_ones() as u64).sum();
        let min_str = format_cents(agg.amount_min);
        let max_str = format_cents(agg.amount_max);
        let sum_str = format_cents(agg.amount_sum);

        use std::fmt::Write;
        let _ = writeln!(
            out_buf,
            "_UNMATCHED {} {} {} {} {} {} {} {}",
            agg.count,
            agg.id_sum,
            sum_str,
            min_str,
            max_str,
            distinct,
            agg.name_bytes,
            agg.note_bytes
        );
    }

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create output dir");
    let out_file_path = out_dir_path.join("aggregates.txt");
    fs::write(&out_file_path, out_buf.as_bytes()).expect("failed to write aggregates.txt");
    let t_out = t_out_0.elapsed();

    let t_total = t0.elapsed();
    eprintln!(
        "Track C v3 [threads={}]: total={:?} (regions={:?}, parse={:?}, merge={:?}, out={:?})",
        num_threads, t_total, t_regions, t_parse, t_merge, t_out
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
    fn test_format_cents_output() {
        assert_eq!(format_cents(1234), "12.34");
        assert_eq!(format_cents(-567), "-5.67");
        assert_eq!(format_cents(0), "0.00");
    }

    #[test]
    fn test_namepool_interning() {
        let mut pool = NamePool::new(16);
        let id0 = pool.intern(b"Alice", hash_name_u64(b"Alice"));
        let id1 = pool.intern(b"Bob", hash_name_u64(b"Bob"));
        let id2 = pool.intern(b"Alice", hash_name_u64(b"Alice"));
        let id_empty = pool.intern(b"", hash_name_u64(b""));
        let id_empty2 = pool.intern(b"", hash_name_u64(b""));

        assert_eq!(id0, id2);
        assert_ne!(id0, id1);
        assert_ne!(id0, id_empty);
        assert_eq!(id_empty, id_empty2);
        assert_eq!(pool.len(), 3);

        let (n0, _) = pool.get_name(id0);
        assert_eq!(n0, b"Alice");
        let (ne, _) = pool.get_name(id_empty);
        assert_eq!(ne, b"");
    }

    #[test]
    fn test_region_lookup_parsing() {
        let data = b"region_id,country\n1,ZZZ\n2,AAA\n5,MMM\n";
        let lookup = RegionLookup::parse(data);
        assert_eq!(lookup.countries, vec![[b'A', b'A', b'A'], [b'M', b'M', b'M'], [b'Z', b'Z', b'Z']]);
        assert_eq!(lookup.get_country(1), 2); // ZZZ
        assert_eq!(lookup.get_country(2), 0); // AAA
        assert_eq!(lookup.get_country(5), 1); // MMM
        assert_eq!(lookup.get_country(999), UNMATCHED_COUNTRY_IDX);
    }

    #[test]
    fn test_country_agg_bitset() {
        let mut agg = CountryAgg::default();
        agg.mark_name(0);
        agg.mark_name(63);
        agg.mark_name(64);
        agg.mark_name(127);
        agg.mark_name(0); // duplicate

        let distinct: u64 = agg.seen_names.iter().map(|&w| w.count_ones() as u64).sum();
        assert_eq!(distinct, 4);
    }
}
