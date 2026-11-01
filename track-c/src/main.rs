use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

const BOM: &[u8] = b"\xEF\xBB\xBF";
const EMPTY_SLOT: u32 = u32::MAX;
const ARENA_FLAG: u32 = 0x8000_0000;

#[inline(always)]
fn hash_name_u64(bytes: &[u8]) -> u64 {
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
    if h == 0 {
        1
    } else {
        h
    }
}

#[cfg(target_os = "linux")]
unsafe fn mmap_readonly(file: &File, len: usize) -> Option<&'static [u8]> {
    use std::os::unix::io::AsRawFd;
    if len == 0 {
        return Some(&[]);
    }
    let fd = file.as_raw_fd();
    let addr: *mut u8;
    std::arch::asm!(
        "syscall",
        in("rax") 9usize, in("rdi") 0usize, in("rsi") len, in("rdx") 1usize,
        in("r10") 2usize, in("r8") fd, in("r9") 0usize,
        lateout("rax") addr, lateout("rcx") _, lateout("r11") _,
    );
    if (addr as isize) < 0 && (addr as isize) > -4096 {
        None
    } else {
        Some(std::slice::from_raw_parts(addr, len))
    }
}

#[cfg(not(target_os = "linux"))]
unsafe fn mmap_readonly(_file: &File, _len: usize) -> Option<&'static [u8]> {
    None
}

fn read_file_or_mmap(path: &Path) -> &'static [u8] {
    let file = match File::open(path) {
        Ok(f) => f,
        Err(_) => return &[],
    };
    let len = file.metadata().map(|m| m.len() as usize).unwrap_or(0);
    if len == 0 {
        return &[];
    }
    if let Some(slice) = unsafe { mmap_readonly(&file, len) } {
        slice
    } else {
        let bytes = std::fs::read(path).unwrap_or_default().into_boxed_slice();
        let ptr = bytes.as_ptr();
        let blen = bytes.len();
        std::mem::forget(bytes);
        unsafe { std::slice::from_raw_parts(ptr, blen) }
    }
}

#[derive(Clone, Copy)]
struct Slot {
    tag: u32,
    offset: u32,
    len: u32,
    id: u32,
}

#[derive(Clone, Copy)]
struct Entry {
    offset: u32,
    len: u32,
    hash: u64,
}

struct NamePool<'a> {
    slots: Vec<Slot>,
    arena: Vec<u8>,
    entries: Vec<Entry>,
    count: usize,
    mask: usize,
    file_data: &'a [u8],
}

impl<'a> NamePool<'a> {
    fn new(cap: usize, file_data: &'a [u8]) -> Self {
        let size = cap.next_power_of_two().max(32768);
        Self {
            slots: vec![
                Slot {
                    tag: 0,
                    offset: 0,
                    len: 0,
                    id: EMPTY_SLOT
                };
                size
            ],
            arena: Vec::with_capacity(4096),
            entries: Vec::with_capacity(size / 2),
            count: 0,
            mask: size - 1,
            file_data,
        }
    }

    #[inline(always)]
    fn get_bytes(&self, offset: u32, len: usize) -> &[u8] {
        if (offset & ARENA_FLAG) != 0 {
            let start = (offset & !ARENA_FLAG) as usize;
            &self.arena[start..start + len]
        } else {
            &self.file_data[offset as usize..(offset as usize) + len]
        }
    }

    fn grow(&mut self) {
        let new_size = self.slots.len() * 2;
        let new_mask = new_size - 1;
        let mut new_slots = vec![
            Slot {
                tag: 0,
                offset: 0,
                len: 0,
                id: EMPTY_SLOT
            };
            new_size
        ];
        for slot in self.slots.iter() {
            if slot.id != EMPTY_SLOT {
                let h64 = self.entries[slot.id as usize].hash;
                let mut idx = (h64 as usize) & new_mask;
                while new_slots[idx].id != EMPTY_SLOT {
                    idx = (idx + 1) & new_mask;
                }
                new_slots[idx] = *slot;
            }
        }
        self.slots = new_slots;
        self.mask = new_mask;
    }

    #[inline(always)]
    fn intern_ref(&mut self, offset: usize, len: usize, h64: u64) -> u32 {
        let tag = (h64 ^ (h64 >> 32)) as u32;
        let mut idx = (h64 as usize) & self.mask;
        let target = &self.file_data[offset..offset + len];
        loop {
            let slot = self.slots[idx];
            if slot.id == EMPTY_SLOT {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern_ref(offset, len, h64);
                }
                let id = self.count as u32;
                let off_u32 = offset as u32;
                self.slots[idx] = Slot {
                    tag,
                    offset: off_u32,
                    len: len as u32,
                    id,
                };
                self.entries.push(Entry {
                    offset: off_u32,
                    len: len as u32,
                    hash: h64,
                });
                self.count += 1;
                return id;
            }
            if slot.tag == tag
                && slot.len as usize == len
                && self.get_bytes(slot.offset, len) == target
            {
                return slot.id;
            }
            idx = (idx + 1) & self.mask;
        }
    }

    #[inline(always)]
    fn intern_slice(&mut self, slice: &[u8], h64: u64) -> u32 {
        let tag = (h64 ^ (h64 >> 32)) as u32;
        let mut idx = (h64 as usize) & self.mask;
        loop {
            let slot = self.slots[idx];
            if slot.id == EMPTY_SLOT {
                if (self.count + 1) * 4 >= self.slots.len() * 3 {
                    self.grow();
                    return self.intern_slice(slice, h64);
                }
                let id = self.count as u32;
                let off = (self.arena.len() as u32) | ARENA_FLAG;
                self.arena.extend_from_slice(slice);
                self.slots[idx] = Slot {
                    tag,
                    offset: off,
                    len: slice.len() as u32,
                    id,
                };
                self.entries.push(Entry {
                    offset: off,
                    len: slice.len() as u32,
                    hash: h64,
                });
                self.count += 1;
                return id;
            }
            if slot.tag == tag
                && slot.len as usize == slice.len()
                && self.get_bytes(slot.offset, slice.len()) == slice
            {
                return slot.id;
            }
            idx = (idx + 1) & self.mask;
        }
    }
}

#[derive(Clone)]
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
    fn new() -> Self {
        Self {
            count: 0,
            id_sum: 0,
            amount_sum: 0,
            amount_min: i64::MAX,
            amount_max: i64::MIN,
            name_bytes: 0,
            note_bytes: 0,
            seen_names: vec![0u64; 2048],
        }
    }

    #[inline(always)]
    fn update(&mut self, id: u64, amount: i64, n_bytes: u64, note_b: u64) {
        self.count += 1;
        self.id_sum += id;
        self.amount_sum += amount;
        self.amount_min = self.amount_min.min(amount);
        self.amount_max = self.amount_max.max(amount);
        self.name_bytes += n_bytes;
        self.note_bytes += note_b;
    }

    #[inline(always)]
    fn mark_name(&mut self, nid: u32) {
        let word_idx = (nid / 64) as usize;
        let mask = 1u64 << (nid % 64);
        if word_idx >= self.seen_names.len() {
            let new_len = (word_idx + 1).next_power_of_two().max(2048);
            self.seen_names.resize(new_len, 0);
        }
        unsafe {
            *self.seen_names.get_unchecked_mut(word_idx) |= mask;
        }
    }
}

struct RegionTable {
    direct: Vec<u16>,
    fallback: HashMap<u32, u16>,
    countries: Vec<[u8; 3]>,
    unmatched_idx: u16,
}

impl RegionTable {
    fn parse(bytes: &[u8]) -> Self {
        let mut pos = 0;
        while pos < bytes.len() && bytes[pos] != b'\n' {
            pos += 1;
        }
        if pos < bytes.len() {
            pos += 1;
        }

        let mut country_map: HashMap<[u8; 3], u16> = HashMap::new();
        let mut country_list = Vec::new();
        let mut direct = vec![u16::MAX; 1_000_000];
        let mut fallback = HashMap::new();

        while pos < bytes.len() {
            if bytes[pos] == b'\n' || bytes[pos] == b'\r' {
                pos += 1;
                continue;
            }
            let mut rid = 0u32;
            while pos < bytes.len() && bytes[pos] != b',' {
                rid = rid * 10 + (bytes[pos] - b'0') as u32;
                pos += 1;
            }
            if pos < bytes.len() {
                pos += 1;
            }
            let c_start = pos;
            while pos < bytes.len() && bytes[pos] != b'\n' && bytes[pos] != b'\r' {
                pos += 1;
            }
            let c_bytes = &bytes[c_start..pos];
            if c_bytes.len() == 3 {
                let code = [c_bytes[0], c_bytes[1], c_bytes[2]];
                let next_idx = country_list.len() as u16;
                let c_idx = *country_map.entry(code).or_insert_with(|| {
                    country_list.push(code);
                    next_idx
                });
                if (rid as usize) < direct.len() {
                    direct[rid as usize] = c_idx;
                } else {
                    fallback.insert(rid, c_idx);
                }
            }
            while pos < bytes.len() && (bytes[pos] == b'\n' || bytes[pos] == b'\r') {
                pos += 1;
            }
        }
        let unmatched_idx = country_list.len() as u16;
        Self {
            direct,
            fallback,
            countries: country_list,
            unmatched_idx,
        }
    }

    #[inline(always)]
    fn get_country(&self, rid: u32) -> usize {
        let r = rid as usize;
        if r < self.direct.len() {
            let c = self.direct[r];
            if c != u16::MAX {
                c as usize
            } else {
                self.unmatched_idx as usize
            }
        } else {
            self.fallback
                .get(&rid)
                .copied()
                .unwrap_or(self.unmatched_idx) as usize
        }
    }
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
    let mut target = chunk_size;
    let mut pos = 0;

    while pos < data.len() && chunk_idx < num_chunks {
        let b = data[pos];
        if b == b'"' {
            in_quote = !in_quote;
        } else if b == b'\n' && !in_quote {
            if pos + 1 >= target {
                boundaries[chunk_idx] = pos + 1;
                chunk_idx += 1;
                target = chunk_idx * chunk_size;
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

struct WorkerState<'a> {
    aggs: Vec<CountryAgg>,
    pool: NamePool<'a>,
}

fn parse_chunk<'a>(
    payload: &'a [u8],
    start: usize,
    end: usize,
    num_countries: usize,
    regions: &RegionTable,
) -> WorkerState<'a> {
    let mut aggs = vec![CountryAgg::new(); num_countries];
    let mut pool = NamePool::new(16384, payload);
    let mut scratch = Vec::with_capacity(256);
    let mut pos = start;

    while pos < end {
        if pos + 3 <= end && &payload[pos..pos + 3] == BOM {
            pos += 3;
        }
        if pos >= end {
            break;
        }

        // Col 0: id
        let mut id = 0u64;
        while pos < end && payload[pos] != b',' {
            id = id * 10 + (payload[pos] - b'0') as u64;
            pos += 1;
        }
        if pos < end {
            pos += 1;
        }

        // Col 1: name
        let (name_len, name_id) = if pos < end && payload[pos] == b',' {
            pos += 1;
            (0u64, pool.intern_slice(b"", hash_name_u64(b"")))
        } else if pos < end && payload[pos] == b'"' {
            pos += 1;
            let start_name = pos;
            let mut unescaped_len = 0usize;
            let mut has_escapes = false;

            while pos < end {
                if payload[pos] == b'"' {
                    if pos + 1 < end && payload[pos + 1] == b'"' {
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
                let mut i = start_name;
                while i < pos - 1 {
                    if payload[i] == b'"' && payload[i + 1] == b'"' {
                        scratch.push(b'"');
                        i += 2;
                    } else {
                        scratch.push(payload[i]);
                        i += 1;
                    }
                }
                let h = hash_name_u64(&scratch);
                pool.intern_slice(&scratch, h)
            } else {
                let slen = (pos - 1) - start_name;
                let h = hash_name_u64(&payload[start_name..start_name + slen]);
                pool.intern_ref(start_name, slen, h)
            };
            if pos < end && payload[pos] == b',' {
                pos += 1;
            }
            (unescaped_len as u64, nid)
        } else {
            let start_name = pos;
            while pos < end && payload[pos] != b',' {
                pos += 1;
            }
            let slen = pos - start_name;
            let h = hash_name_u64(&payload[start_name..pos]);
            let nid = pool.intern_ref(start_name, slen, h);
            if pos < end {
                pos += 1;
            }
            (slen as u64, nid)
        };

        // Col 2: note
        let note_len: u64 = if pos < end && payload[pos] == b',' {
            pos += 1;
            0
        } else if pos < end && payload[pos] == b'"' {
            pos += 1;
            let mut unescaped = 0u64;
            while pos < end {
                if payload[pos] == b'"' {
                    if pos + 1 < end && payload[pos + 1] == b'"' {
                        unescaped += 1;
                        pos += 2;
                    } else {
                        pos += 1;
                        break;
                    }
                } else {
                    unescaped += 1;
                    pos += 1;
                }
            }
            if pos < end && payload[pos] == b',' {
                pos += 1;
            }
            unescaped
        } else {
            let start_note = pos;
            while pos < end && payload[pos] != b',' {
                pos += 1;
            }
            let len = (pos - start_note) as u64;
            if pos < end {
                pos += 1;
            }
            len
        };

        // Col 3: region_id
        let mut rid = 0u32;
        while pos < end && payload[pos] != b',' {
            rid = rid * 10 + (payload[pos] - b'0') as u32;
            pos += 1;
        }
        if pos < end {
            pos += 1;
        }

        // Col 4: amount
        let neg = if pos < end && payload[pos] == b'-' {
            pos += 1;
            true
        } else {
            false
        };
        let mut whole = 0i64;
        while pos < end && payload[pos] != b'.' {
            whole = whole * 10 + (payload[pos] - b'0') as i64;
            pos += 1;
        }
        if pos < end && payload[pos] == b'.' {
            pos += 1;
        }
        let mut cents = whole * 100;
        if pos < end && payload[pos] >= b'0' && payload[pos] <= b'9' {
            cents += (payload[pos] - b'0') as i64 * 10;
            pos += 1;
        }
        if pos < end && payload[pos] >= b'0' && payload[pos] <= b'9' {
            cents += (payload[pos] - b'0') as i64;
            pos += 1;
        }
        if neg {
            cents = -cents;
        }
        while pos < end && (payload[pos] == b'\r' || payload[pos] == b'\n') {
            pos += 1;
        }

        let c_idx = regions.get_country(rid);
        aggs[c_idx].update(id, cents, name_len, note_len);
        aggs[c_idx].mark_name(name_id);
    }
    WorkerState { aggs, pool }
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

fn write_line(out: &mut Vec<u8>, code: &[u8], agg: &CountryAgg) {
    out.extend_from_slice(code);
    out.push(b' ');
    write_u64(out, agg.count);
    out.push(b' ');
    write_u64(out, agg.id_sum);
    out.push(b' ');
    write_money(out, agg.amount_sum);
    out.push(b' ');
    write_money(out, agg.amount_min);
    out.push(b' ');
    write_money(out, agg.amount_max);
    out.push(b' ');
    let distinct: u64 = agg.seen_names.iter().map(|w| w.count_ones() as u64).sum();
    write_u64(out, distinct);
    out.push(b' ');
    write_u64(out, agg.name_bytes);
    out.push(b' ');
    write_u64(out, agg.note_bytes);
    out.push(b'\n');
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let out_path = Path::new(out_dir).join("aggregates.txt");
    let reg_path = Path::new(data_dir).join("regions.csv");
    let rec_path = Path::new(data_dir).join("records.csv");

    let reg_data = read_file_or_mmap(&reg_path);
    let rec_data = read_file_or_mmap(&rec_path);

    if reg_data.is_empty() || rec_data.is_empty() {
        let _ = File::create(&out_path);
        return;
    }

    let regions = RegionTable::parse(reg_data);
    let num_countries = (regions.unmatched_idx + 1) as usize;

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
    let num_workers = 4;
    let boundaries = find_chunk_boundaries(payload, num_workers);

    let mut worker_states: Vec<WorkerState> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_workers);
        for i in 0..num_workers {
            let chunk_start = boundaries[i];
            let chunk_end = boundaries[i + 1];
            let r_ref = &regions;
            handles.push(
                s.spawn(move || parse_chunk(payload, chunk_start, chunk_end, num_countries, r_ref)),
            );
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    // Destructive merge into worker 0
    let mut base = worker_states.swap_remove(0);
    let mut remap_buf = Vec::with_capacity(16384);

    while !worker_states.is_empty() {
        let mut other = worker_states.pop().unwrap();
        remap_buf.clear();
        let other_count = other.pool.count;
        for i in 0..other_count {
            let entry = other.pool.entries[i];
            let bytes = other.pool.get_bytes(entry.offset, entry.len as usize);
            let global_id = base.pool.intern_slice(bytes, entry.hash);
            remap_buf.push(global_id);
        }
        drop(other.pool);

        for c in 0..num_countries {
            let o_agg = &mut other.aggs[c];
            if o_agg.count == 0 {
                continue;
            }
            let b_agg = &mut base.aggs[c];
            if b_agg.count == 0 {
                b_agg.amount_min = o_agg.amount_min;
                b_agg.amount_max = o_agg.amount_max;
            } else {
                b_agg.amount_min = b_agg.amount_min.min(o_agg.amount_min);
                b_agg.amount_max = b_agg.amount_max.max(o_agg.amount_max);
            }
            b_agg.count += o_agg.count;
            b_agg.id_sum += o_agg.id_sum;
            b_agg.amount_sum += o_agg.amount_sum;
            b_agg.name_bytes += o_agg.name_bytes;
            b_agg.note_bytes += o_agg.note_bytes;

            for (w_idx, &word) in o_agg.seen_names.iter().enumerate() {
                if word == 0 {
                    continue;
                }
                let mut temp = word;
                let mut bit_idx = 0;
                while temp > 0 {
                    if (temp & 1) != 0 {
                        let other_nid = (w_idx * 64 + bit_idx) as u32;
                        let global_nid = remap_buf[other_nid as usize];
                        b_agg.mark_name(global_nid);
                    }
                    temp >>= 1;
                    bit_idx += 1;
                }
            }
        }
    }

    let mut active_indices = Vec::new();
    for i in 0..regions.unmatched_idx as usize {
        if base.aggs[i].count > 0 {
            active_indices.push(i);
        }
    }
    active_indices.sort_unstable_by_key(|&i| regions.countries[i]);

    let mut out_file = File::create(&out_path).unwrap();
    let mut out_buf = Vec::with_capacity(64 * 1024);

    for idx in active_indices {
        write_line(&mut out_buf, &regions.countries[idx], &base.aggs[idx]);
    }
    let u_idx = regions.unmatched_idx as usize;
    if base.aggs[u_idx].count > 0 {
        write_line(&mut out_buf, b"_UNMATCHED", &base.aggs[u_idx]);
    }

    if !out_buf.is_empty() {
        out_file.write_all(&out_buf).unwrap();
    }
}
