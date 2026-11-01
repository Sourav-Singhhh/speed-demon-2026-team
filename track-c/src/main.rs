use std::env;
use std::fs;
use std::path::Path;

const BOM: &[u8] = b"\xEF\xBB\xBF";
const UNMATCHED_COUNTRY_IDX: usize = 240;

#[inline(always)]
pub fn hash_name_u64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    let mut i = 0;
    while i + 8 <= bytes.len() {
        let chunk = u64::from_ne_bytes(bytes[i..i + 8].try_into().unwrap());
        h ^= chunk;
        h = h.wrapping_mul(0x100000001b3);
        i += 8;
    }
    while i < bytes.len() {
        h ^= bytes[i] as u64;
        h = h.wrapping_mul(0x100000001b3);
        i += 1;
    }
    h
}

#[cfg(target_os = "linux")]
fn mmap_file(file: &fs::File, len: usize) -> Result<&'static [u8], String> {
    use std::os::unix::io::AsRawFd;
    if len == 0 {
        return Ok(&[]);
    }
    let fd = file.as_raw_fd();
    let addr: *mut u8;
    unsafe {
        std::arch::asm!(
            "syscall",
            in("rax") 9usize, // sys_mmap
            in("rdi") 0usize, // addr = NULL
            in("rsi") len,   // length
            in("rdx") 1usize, // PROT_READ
            in("r10") 2usize, // MAP_PRIVATE
            in("r8") fd,     // fd
            in("r9") 0usize, // offset = 0
            lateout("rax") addr,
            lateout("rcx") _,
            lateout("r11") _,
        );
    }
    if (addr as isize) < 0 && (addr as isize) > -4096 {
        return Err(format!("mmap failed with errno {}", -(addr as isize)));
    }
    unsafe { Ok(std::slice::from_raw_parts(addr, len)) }
}

#[cfg(not(target_os = "linux"))]
fn mmap_file(_file: &fs::File, _len: usize) -> Result<&'static [u8], String> {
    Err("mmap only on linux".to_string())
}

fn read_file_bytes(path: &Path) -> Result<&'static [u8], String> {
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let len = file.metadata().map_err(|e| e.to_string())?.len() as usize;
    if let Ok(mapped) = mmap_file(&file, len) {
        Ok(mapped)
    } else {
        let bytes = fs::read(path).map_err(|e| e.to_string())?;
        let boxed = bytes.into_boxed_slice();
        let out = unsafe { std::slice::from_raw_parts(boxed.as_ptr(), boxed.len()) };
        std::mem::forget(boxed);
        Ok(out)
    }
}

struct RegionLookup {
    region_to_country: Vec<u8>,
    hash_keys: Vec<u32>,
    hash_values: Vec<u8>,
    hash_mask: usize,
    countries: Vec<[u8; 3]>,
    use_hash: bool,
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
        // Single pass: collect (rid, code_idx) and unique countries
        let mut max_region = 0usize;
        let mut entries = Vec::with_capacity(131072);
        while pos < data.len() {
            let mut rid = 0usize;
            while pos < data.len() && data[pos] != b',' {
                let b = data[pos];
                rid = rid * 10 + (b.wrapping_sub(b'0')) as usize;
                pos += 1;
            }
            if pos < data.len() && data[pos] == b',' {
                pos += 1;
            }
            if rid > max_region {
                max_region = rid;
            }

            if pos + 3 <= data.len()
                && data[pos] >= b'A'
                && data[pos] <= b'Z'
                && data[pos + 1] >= b'A'
                && data[pos + 1] <= b'Z'
                && data[pos + 2] >= b'A'
                && data[pos + 2] <= b'Z'
            {
                let c0 = (data[pos] - b'A') as usize;
                let c1 = (data[pos + 1] - b'A') as usize;
                let c2 = (data[pos + 2] - b'A') as usize;
                let code_idx = (c0 * 676 + c1 * 26 + c2) as u16;
                entries.push((rid as u32, code_idx));
                if !country_seen[code_idx as usize] {
                    country_seen[code_idx as usize] = true;
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

        if max_region <= 1_500_000 {
            let mut region_to_country = vec![UNMATCHED_COUNTRY_IDX as u8; max_region + 1];
            for (rid, code_idx) in entries {
                region_to_country[rid as usize] = code_to_country[code_idx as usize];
            }
            Self {
                region_to_country,
                hash_keys: Vec::new(),
                hash_values: Vec::new(),
                hash_mask: 0,
                countries: country_names,
                use_hash: false,
            }
        } else {
            let hash_cap = 262144;
            let hash_mask = hash_cap - 1;
            let mut hash_keys = vec![0u32; hash_cap];
            let mut hash_values = vec![UNMATCHED_COUNTRY_IDX as u8; hash_cap];
            for (rid, code_idx) in entries {
                let mut idx = (rid.wrapping_mul(0x9E3779B9) as usize) & hash_mask;
                while hash_keys[idx] != 0 && hash_keys[idx] != rid {
                    idx = (idx + 1) & hash_mask;
                }
                hash_keys[idx] = rid;
                hash_values[idx] = code_to_country[code_idx as usize];
            }
            Self {
                region_to_country: Vec::new(),
                hash_keys,
                hash_values,
                hash_mask,
                countries: country_names,
                use_hash: true,
            }
        }
    }

    #[inline(always)]
    fn get_country(&self, rid: usize) -> usize {
        if !self.use_hash {
            if rid < self.region_to_country.len() {
                unsafe { *self.region_to_country.get_unchecked(rid) as usize }
            } else {
                UNMATCHED_COUNTRY_IDX
            }
        } else {
            let mut idx = ((rid as u32).wrapping_mul(0x9E3779B9) as usize) & self.hash_mask;
            loop {
                let k = self.hash_keys[idx];
                if k == rid as u32 {
                    return self.hash_values[idx] as usize;
                }
                if k == 0 {
                    return UNMATCHED_COUNTRY_IDX;
                }
                idx = (idx + 1) & self.hash_mask;
            }
        }
    }
}

const NAME_EMPTY_SENTINEL: u32 = 0xFFFF_FFFF;
const ARENA_FLAG: u32 = 0x8000_0000;

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

pub struct NamePool<'a> {
    slots: Vec<NameSlot>,
    arena: Vec<u8>,
    entries: Vec<NameEntry>,
    count: usize,
    mask: usize,
    file_data: &'a [u8],
}

impl<'a> NamePool<'a> {
    pub fn new(capacity: usize, file_data: &'a [u8]) -> Self {
        let cap = capacity.next_power_of_two().max(1024);
        Self {
            slots: vec![NameSlot::default(); cap],
            arena: Vec::with_capacity(4096),
            entries: Vec::with_capacity(cap / 2),
            count: 0,
            mask: cap - 1,
            file_data,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }

    #[inline(always)]
    fn get_name_bytes(&self, offset: u32, len: usize) -> &[u8] {
        if (offset & ARENA_FLAG) != 0 {
            let start = (offset & !ARENA_FLAG) as usize;
            &self.arena[start..start + len]
        } else {
            let start = offset as usize;
            &self.file_data[start..start + len]
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
    pub fn intern_ref(&mut self, file_offset: usize, len: usize, h64: u64) -> u32 {
        let tag = hash_tag_from_u64(h64);
        let mut idx = (h64 as usize) & self.mask;
        let target = &self.file_data[file_offset..file_offset + len];

        loop {
            let slot = self.slots[idx];
            if slot.name_id == NAME_EMPTY_SENTINEL {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern_ref(file_offset, len, h64);
                }

                let id = self.count as u32;
                let off_u32 = file_offset as u32;
                self.slots[idx] = NameSlot {
                    hash_tag: tag,
                    offset: off_u32,
                    len: len as u32,
                    name_id: id,
                };
                self.entries.push(NameEntry { offset: off_u32, len: len as u32, hash: h64 });
                self.count += 1;
                return id;
            }

            if slot.hash_tag == tag && slot.len as usize == len {
                let bytes = self.get_name_bytes(slot.offset, len);
                if bytes == target {
                    return slot.name_id;
                }
            }
            idx = (idx + 1) & self.mask;
        }
    }

    #[inline(always)]
    pub fn intern_slice(&mut self, name: &[u8], h64: u64) -> u32 {
        let tag = hash_tag_from_u64(h64);
        let mut idx = (h64 as usize) & self.mask;

        loop {
            let slot = self.slots[idx];
            if slot.name_id == NAME_EMPTY_SENTINEL {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern_slice(name, h64);
                }

                let off = self.arena.len() as u32;
                self.arena.extend_from_slice(name);
                let off_u32 = off | ARENA_FLAG;

                let id = self.count as u32;
                self.slots[idx] = NameSlot {
                    hash_tag: tag,
                    offset: off_u32,
                    len: name.len() as u32,
                    name_id: id,
                };
                self.entries.push(NameEntry { offset: off_u32, len: name.len() as u32, hash: h64 });
                self.count += 1;
                return id;
            }

            if slot.hash_tag == tag && slot.len as usize == name.len() {
                let bytes = self.get_name_bytes(slot.offset, name.len());
                if bytes == name {
                    return slot.name_id;
                }
            }
            idx = (idx + 1) & self.mask;
        }
    }

    #[inline(always)]
    pub fn get_name(&self, id: u32) -> (&[u8], u64) {
        let entry = self.entries[id as usize];
        let bytes = self.get_name_bytes(entry.offset, entry.len as usize);
        (bytes, entry.hash)
    }
}

#[derive(Default, Clone)]
struct CountryAgg {
    count: u64,
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
            let new_len = (word_idx + 1).next_power_of_two().max(16);
            self.seen_names.resize(new_len, 0);
        }
        self.seen_names[word_idx] |= bit_mask;
    }

    #[inline(always)]
    fn mark_name_fast(&mut self, name_id: u32) {
        let word_idx = (name_id / 64) as usize;
        let bit_mask = 1u64 << (name_id % 64);
        if word_idx >= self.seen_names.len() {
            let new_len = (word_idx + 1).next_power_of_two().max(2048);
            self.seen_names.resize(new_len, 0);
        }
        unsafe {
            *self.seen_names.get_unchecked_mut(word_idx) |= bit_mask;
        }
    }
}

struct WorkerState<'a> {
    aggs: Vec<CountryAgg>,
    pool: NamePool<'a>,
}

fn parse_records_chunk<'a>(
    full_payload: &'a [u8],
    chunk_start: usize,
    chunk_end: usize,
    lookup: &RegionLookup,
) -> WorkerState<'a> {
    let mut aggs = vec![CountryAgg {
        amount_min: i64::MAX,
        amount_max: i64::MIN,
        ..Default::default()
    }; UNMATCHED_COUNTRY_IDX + 1];

    let mut pool = NamePool::new(32768, full_payload);
    let mut pos = chunk_start;
    let end = chunk_end;
    let mut scratch = Vec::with_capacity(256);

    while pos < end {
        if pos + 2 < end && &full_payload[pos..pos + 3] == BOM {
            pos += 3;
        }
        if pos >= end {
            break;
        }

        // Col 0: id
        let mut id_val = 0u64;
        while pos < end && full_payload[pos] != b',' {
            let b = full_payload[pos];
            id_val = id_val * 10 + (b - b'0') as u64;
            pos += 1;
        }
        if pos < end && full_payload[pos] == b',' {
            pos += 1;
        }

        // Col 1: name
        let (name_len, name_id) = if pos < end && full_payload[pos] == b',' {
            pos += 1;
            let nid = pool.intern_slice(b"", hash_name_u64(b""));
            (0u64, nid)
        } else if pos < end && full_payload[pos] == b'"' {
            pos += 1;
            let mut unescaped_len = 0usize;
            let mut has_escapes = false;
            let start_name = pos;
            while pos < end {
                let b = full_payload[pos];
                if b == b'"' {
                    if pos + 1 < end && full_payload[pos + 1] == b'"' {
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
                    if full_payload[i] == b'"' && full_payload[i + 1] == b'"' {
                        scratch.push(b'"');
                        i += 2;
                    } else {
                        scratch.push(full_payload[i]);
                        i += 1;
                    }
                }
                let h = hash_name_u64(&scratch);
                pool.intern_slice(&scratch, h)
            } else {
                let slice_len = (pos - 1) - start_name;
                let h = hash_name_u64(&full_payload[start_name..start_name + slice_len]);
                pool.intern_ref(start_name, slice_len, h)
            };
            if pos < end && full_payload[pos] == b',' {
                pos += 1;
            }
            (unescaped_len as u64, nid)
        } else {
            let start_name = pos;
            while pos < end && full_payload[pos] != b',' {
                pos += 1;
            }
            let len = pos - start_name;
            let h = hash_name_u64(&full_payload[start_name..pos]);
            let nid = pool.intern_ref(start_name, len, h);
            if pos < end && full_payload[pos] == b',' {
                pos += 1;
            }
            (len as u64, nid)
        };

        // Col 2: note
        let note_len: u64 = if pos < end && full_payload[pos] == b',' {
            pos += 1;
            0
        } else if pos < end && full_payload[pos] == b'"' {
            pos += 1;
            let start_note = pos;
            let mut num_quotes = 0usize;
            while pos < end {
                if full_payload[pos] == b'"' {
                    if pos + 1 < end && full_payload[pos + 1] == b'"' {
                        num_quotes += 1;
                        pos += 2;
                    } else {
                        pos += 1;
                        break;
                    }
                } else {
                    pos += 1;
                }
            }
            let raw_len = (pos - 1) - start_note;
            if pos < end && full_payload[pos] == b',' {
                pos += 1;
            }
            (raw_len - num_quotes) as u64
        } else {
            let start_note = pos;
            while pos < end && full_payload[pos] != b',' {
                pos += 1;
            }
            let len = (pos - start_note) as u64;
            if pos < end && full_payload[pos] == b',' {
                pos += 1;
            }
            len
        };

        // Col 3: region_id
        let mut region_val = 0usize;
        while pos < end && full_payload[pos] != b',' {
            let b = full_payload[pos];
            region_val = region_val * 10 + (b - b'0') as usize;
            pos += 1;
        }
        if pos < end && full_payload[pos] == b',' {
            pos += 1;
        }

        // Col 4: amount
        let mut neg = false;
        if pos < end && full_payload[pos] == b'-' {
            neg = true;
            pos += 1;
        }
        let mut dollars = 0i64;
        while pos < end && full_payload[pos] != b'.' && full_payload[pos] != b'\r' && full_payload[pos] != b'\n' {
            let b = full_payload[pos];
            dollars = dollars * 10 + (b - b'0') as i64;
            pos += 1;
        }
        let mut cents = dollars * 100;
        if pos < end && full_payload[pos] == b'.' {
            pos += 1;
            if pos < end && full_payload[pos] >= b'0' && full_payload[pos] <= b'9' {
                cents += ((full_payload[pos] - b'0') as i64) * 10;
                pos += 1;
            }
            if pos < end && full_payload[pos] >= b'0' && full_payload[pos] <= b'9' {
                cents += (full_payload[pos] - b'0') as i64;
                pos += 1;
            }
        }
        if neg {
            cents = -cents;
        }
        if pos < end && full_payload[pos] == b'\r' {
            pos += 1;
        }
        if pos < end && full_payload[pos] == b'\n' {
            pos += 1;
        }

        // Grouping & aggregation
        let c_idx = lookup.get_country(region_val);
        let agg = &mut aggs[c_idx];
        agg.count += 1;
        agg.id_sum += id_val;
        agg.amount_sum += cents;
        if cents < agg.amount_min {
            agg.amount_min = cents;
        }
        if cents > agg.amount_max {
            agg.amount_max = cents;
        }
        agg.name_bytes += name_len;
        agg.note_bytes += note_len;
        agg.mark_name(name_id);
    }

    WorkerState { aggs, pool }
}

fn find_chunk_boundaries(data: &[u8], num_chunks: usize) -> Vec<usize> {
    if num_chunks <= 1 {
        return vec![0, data.len()];
    }

    let chunk_size = data.len() / num_chunks;
    let mut boundaries = vec![0; num_chunks + 1];
    boundaries[num_chunks] = data.len();

    let mut in_quote = false;
    let mut chunk_idx = 1;
    let mut next_target = chunk_size;

    let mut pos = 0;
    while pos < data.len() && chunk_idx < num_chunks {
        let b = data[pos];
        if b == b'"' {
            in_quote = !in_quote;
        } else if b == b'\n' && !in_quote {
            let next_line_start = pos + 1;
            if next_line_start >= next_target {
                boundaries[chunk_idx] = next_line_start;
                chunk_idx += 1;
                next_target = chunk_idx * chunk_size;
            }
        }
        pos += 1;
    }

    while chunk_idx < num_chunks {
        boundaries[chunk_idx] = data.len();
        chunk_idx += 1;
    }

    boundaries
}

fn write_money(out: &mut Vec<u8>, cents: i64) {
    if cents < 0 {
        out.push(b'-');
    }
    let abs_cents = cents.unsigned_abs();
    let dollars = abs_cents / 100;
    let rem = abs_cents % 100;

    let mut tmp = [0u8; 24];
    let mut i = 0;
    let mut d = dollars;
    if d == 0 {
        tmp[i] = b'0';
        i += 1;
    } else {
        while d > 0 {
            tmp[i] = b'0' + (d % 10) as u8;
            d /= 10;
            i += 1;
        }
    }
    while i > 0 {
        i -= 1;
        out.push(tmp[i]);
    }

    out.push(b'.');
    out.push(b'0' + (rem / 10) as u8);
    out.push(b'0' + (rem % 10) as u8);
}

fn write_u64(out: &mut Vec<u8>, mut val: u64) {
    if val == 0 {
        out.push(b'0');
        return;
    }
    let mut tmp = [0u8; 24];
    let mut i = 0;
    while val > 0 {
        tmp[i] = b'0' + (val % 10) as u8;
        val /= 10;
        i += 1;
    }
    while i > 0 {
        i -= 1;
        out.push(tmp[i]);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("create out dir failed");
    let out_file = out_dir_path.join("aggregates.txt");

    let reg_path = Path::new(data_dir).join("regions.csv");
    let rec_path = Path::new(data_dir).join("records.csv");

    let reg_data = read_file_bytes(&reg_path).expect("open regions.csv failed");
    let rec_data = read_file_bytes(&rec_path).expect("open records.csv failed");

    let lookup = RegionLookup::parse(reg_data);

    let mut start_pos = 0;
    if rec_data.starts_with(BOM) {
        start_pos += 3;
    }
    while start_pos < rec_data.len() && rec_data[start_pos] != b'\n' {
        start_pos += 1;
    }
    if start_pos < rec_data.len() && rec_data[start_pos] == b'\n' {
        start_pos += 1;
    }

    let payload = &rec_data[start_pos..];
    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(4)
        .clamp(1, 16);

    let num_chunks = num_threads;
    let boundaries = find_chunk_boundaries(payload, num_chunks);

    let mut chunk_results: Vec<WorkerState> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_chunks);
        for i in 0..num_chunks {
            let start = boundaries[i];
            let end = boundaries[i + 1];
            let l_ref = &lookup;
            handles.push(s.spawn(move || {
                parse_records_chunk(payload, start, end, l_ref)
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    // Merge into worker 0 destructively
    let mut base_state = chunk_results.swap_remove(0);
    for agg in base_state.aggs.iter_mut() {
        if agg.count > 0 && agg.seen_names.len() < 2048 {
            agg.seen_names.resize(2048, 0);
        }
    }
    let mut remap_buf = Vec::with_capacity(32 * 1024);

    while !chunk_results.is_empty() {
        let mut other_worker = chunk_results.pop().unwrap();
        remap_buf.clear();
        let other_count = other_worker.pool.len();
        for i in 0..other_count {
            let (name, h) = other_worker.pool.get_name(i as u32);
            let global_id = base_state.pool.intern_slice(name, h);
            remap_buf.push(global_id);
        }
        drop(other_worker.pool);

        for c in 0..=UNMATCHED_COUNTRY_IDX {
            let other_agg = &mut other_worker.aggs[c];
            if other_agg.count == 0 {
                continue;
            }
            let base_agg = &mut base_state.aggs[c];
            if base_agg.count == 0 {
                base_agg.amount_min = other_agg.amount_min;
                base_agg.amount_max = other_agg.amount_max;
            } else {
                if other_agg.amount_min < base_agg.amount_min {
                    base_agg.amount_min = other_agg.amount_min;
                }
                if other_agg.amount_max > base_agg.amount_max {
                    base_agg.amount_max = other_agg.amount_max;
                }
            }
            base_agg.count += other_agg.count;
            base_agg.id_sum += other_agg.id_sum;
            base_agg.amount_sum += other_agg.amount_sum;
            base_agg.name_bytes += other_agg.name_bytes;
            base_agg.note_bytes += other_agg.note_bytes;

            for (w_idx, &word) in other_agg.seen_names.iter().enumerate() {
                if word == 0 {
                    continue;
                }
                let mut bit_idx = 0;
                let mut temp = word;
                while temp > 0 {
                    if temp & 1 != 0 {
                        let other_nid = (w_idx * 64 + bit_idx) as u32;
                        let global_nid = remap_buf[other_nid as usize];
                        base_agg.mark_name_fast(global_nid);
                    }
                    temp >>= 1;
                    bit_idx += 1;
                }
            }
        }
    }

    // Output formatting
    let mut out_buf = Vec::with_capacity(64 * 1024);
    for (i, c_code) in lookup.countries.iter().enumerate() {
        let agg = &base_state.aggs[i];
        if agg.count == 0 {
            continue;
        }
        out_buf.extend_from_slice(c_code);
        out_buf.push(b' ');
        write_u64(&mut out_buf, agg.count);
        out_buf.push(b' ');
        write_u64(&mut out_buf, agg.id_sum);
        out_buf.push(b' ');
        write_money(&mut out_buf, agg.amount_sum);
        out_buf.push(b' ');
        write_money(&mut out_buf, agg.amount_min);
        out_buf.push(b' ');
        write_money(&mut out_buf, agg.amount_max);
        out_buf.push(b' ');

        let distinct_names: u64 = agg.seen_names.iter().map(|w| w.count_ones() as u64).sum();
        write_u64(&mut out_buf, distinct_names);
        out_buf.push(b' ');
        write_u64(&mut out_buf, agg.name_bytes);
        out_buf.push(b' ');
        write_u64(&mut out_buf, agg.note_bytes);
        out_buf.push(b'\n');
    }

    // Unmatched country
    let un_agg = &base_state.aggs[UNMATCHED_COUNTRY_IDX];
    if un_agg.count > 0 {
        out_buf.extend_from_slice(b"_UNMATCHED ");
        write_u64(&mut out_buf, un_agg.count);
        out_buf.push(b' ');
        write_u64(&mut out_buf, un_agg.id_sum);
        out_buf.push(b' ');
        write_money(&mut out_buf, un_agg.amount_sum);
        out_buf.push(b' ');
        write_money(&mut out_buf, un_agg.amount_min);
        out_buf.push(b' ');
        write_money(&mut out_buf, un_agg.amount_max);
        out_buf.push(b' ');

        let distinct_names: u64 = un_agg.seen_names.iter().map(|w| w.count_ones() as u64).sum();
        write_u64(&mut out_buf, distinct_names);
        out_buf.push(b' ');
        write_u64(&mut out_buf, un_agg.name_bytes);
        out_buf.push(b' ');
        write_u64(&mut out_buf, un_agg.note_bytes);
        out_buf.push(b'\n');
    }

    fs::write(&out_file, out_buf).expect("write aggregates.txt failed");
}
