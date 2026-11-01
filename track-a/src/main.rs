use std::env;
use std::fs::File;
use std::io::Write;
use std::thread;

const HOURS: usize = 72;
const MAX_EP_SLOTS: usize = 4096;

#[derive(Clone, Copy)]
struct EpSlot {
    hash: u64,
    offset: u32,
    len: u16,
    id: u16,
}

struct EpTable {
    slots: Vec<EpSlot>,
    endpoints: Vec<(usize, usize)>, // (offset, len) in mmap
}

impl EpTable {
    fn new() -> Self {
        Self {
            slots: vec![
                EpSlot {
                    hash: 0,
                    offset: 0,
                    len: 0,
                    id: u16::MAX
                };
                MAX_EP_SLOTS
            ],
            endpoints: Vec::with_capacity(2048),
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

    fn get_or_insert(&mut self, mmap: &[u8], offset: usize, len: usize) -> u16 {
        let ep_bytes = &mmap[offset..offset + len];
        let h = Self::hash_bytes(ep_bytes);
        let mask = self.slots.len() - 1;
        let mut idx = (h as usize) & mask;
        loop {
            let slot = &self.slots[idx];
            if slot.id == u16::MAX {
                let id = self.endpoints.len() as u16;
                self.slots[idx] = EpSlot {
                    hash: h,
                    offset: offset as u32,
                    len: len as u16,
                    id,
                };
                self.endpoints.push((offset, len));
                return id;
            }
            if slot.hash == h && slot.len as usize == len {
                let existing = &mmap[slot.offset as usize..slot.offset as usize + len];
                if existing == ep_bytes {
                    return slot.id;
                }
            }
            idx = (idx + 1) & mask;
        }
    }

    #[inline(always)]
    fn lookup(&self, mmap: &[u8], ep_bytes: &[u8]) -> Option<u16> {
        let h = Self::hash_bytes(ep_bytes);
        let mask = self.slots.len() - 1;
        let mut idx = (h as usize) & mask;
        loop {
            let slot = &self.slots[idx];
            if slot.id == u16::MAX {
                return None;
            }
            if slot.hash == h && slot.len as usize == ep_bytes.len() {
                let existing = &mmap[slot.offset as usize..slot.offset as usize + ep_bytes.len()];
                if existing == ep_bytes {
                    return Some(slot.id);
                }
            }
            idx = (idx + 1) & mask;
        }
    }
}

// Map RFC 3339 timestamps for 2026-10-30T18..2026-11-02T18 to 0..71
#[inline(always)]
fn parse_hour_idx(ts: &[u8]) -> usize {
    let month = ts[6] - b'0';
    let day = (ts[8] - b'0') * 10 + (ts[9] - b'0');
    let day_off = if month == 0 {
        (day - 30) as usize
    } else {
        (2 + day - 1) as usize
    };
    let h = ((ts[11] - b'0') * 10 + (ts[12] - b'0')) as usize;
    day_off * 24 + h - 18
}

const HOUR_STRINGS: [&str; 72] = [
    "2026-10-30T18:00:00Z",
    "2026-10-30T19:00:00Z",
    "2026-10-30T20:00:00Z",
    "2026-10-30T21:00:00Z",
    "2026-10-30T22:00:00Z",
    "2026-10-30T23:00:00Z",
    "2026-10-31T00:00:00Z",
    "2026-10-31T01:00:00Z",
    "2026-10-31T02:00:00Z",
    "2026-10-31T03:00:00Z",
    "2026-10-31T04:00:00Z",
    "2026-10-31T05:00:00Z",
    "2026-10-31T06:00:00Z",
    "2026-10-31T07:00:00Z",
    "2026-10-31T08:00:00Z",
    "2026-10-31T09:00:00Z",
    "2026-10-31T10:00:00Z",
    "2026-10-31T11:00:00Z",
    "2026-10-31T12:00:00Z",
    "2026-10-31T13:00:00Z",
    "2026-10-31T14:00:00Z",
    "2026-10-31T15:00:00Z",
    "2026-10-31T16:00:00Z",
    "2026-10-31T17:00:00Z",
    "2026-10-31T18:00:00Z",
    "2026-10-31T19:00:00Z",
    "2026-10-31T20:00:00Z",
    "2026-10-31T21:00:00Z",
    "2026-10-31T22:00:00Z",
    "2026-10-31T23:00:00Z",
    "2026-11-01T00:00:00Z",
    "2026-11-01T01:00:00Z",
    "2026-11-01T02:00:00Z",
    "2026-11-01T03:00:00Z",
    "2026-11-01T04:00:00Z",
    "2026-11-01T05:00:00Z",
    "2026-11-01T06:00:00Z",
    "2026-11-01T07:00:00Z",
    "2026-11-01T08:00:00Z",
    "2026-11-01T09:00:00Z",
    "2026-11-01T10:00:00Z",
    "2026-11-01T11:00:00Z",
    "2026-11-01T12:00:00Z",
    "2026-11-01T13:00:00Z",
    "2026-11-01T14:00:00Z",
    "2026-11-01T15:00:00Z",
    "2026-11-01T16:00:00Z",
    "2026-11-01T17:00:00Z",
    "2026-11-01T18:00:00Z",
    "2026-11-01T19:00:00Z",
    "2026-11-01T20:00:00Z",
    "2026-11-01T21:00:00Z",
    "2026-11-01T22:00:00Z",
    "2026-11-01T23:00:00Z",
    "2026-11-02T00:00:00Z",
    "2026-11-02T01:00:00Z",
    "2026-11-02T02:00:00Z",
    "2026-11-02T03:00:00Z",
    "2026-11-02T04:00:00Z",
    "2026-11-02T05:00:00Z",
    "2026-11-02T06:00:00Z",
    "2026-11-02T07:00:00Z",
    "2026-11-02T08:00:00Z",
    "2026-11-02T09:00:00Z",
    "2026-11-02T10:00:00Z",
    "2026-11-02T11:00:00Z",
    "2026-11-02T12:00:00Z",
    "2026-11-02T13:00:00Z",
    "2026-11-02T14:00:00Z",
    "2026-11-02T15:00:00Z",
    "2026-11-02T16:00:00Z",
    "2026-11-02T17:00:00Z",
];

#[inline(always)]
fn parse_u32(mut s: &[u8]) -> u32 {
    let mut n: u32 = 0;
    while !s.is_empty() && s[0] >= b'0' && s[0] <= b'9' {
        n = n * 10 + (s[0] - b'0') as u32;
        s = &s[1..];
    }
    n
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: solution <data_dir> <out_dir>");
        std::process::exit(1);
    }
    let data_dir = &args[1];
    let out_dir = &args[2];
    let in_path = format!("{}/requests.log", data_dir);
    let out_path = format!("{}/summary.txt", out_dir);

    let mmap = unsafe {
        let f = match File::open(&in_path) {
            Ok(file) => file,
            Err(_) => {
                let _ = File::create(&out_path);
                return;
            }
        };
        let m = match memmap2_minimal(&f) {
            Some(m) => m,
            None => {
                let _ = File::create(&out_path);
                return;
            }
        };
        m
    };

    if mmap.is_empty() {
        let _ = File::create(&out_path);
        return;
    }

    // Step 1: Discover unique endpoints and build global catalog
    let mut ep_table = EpTable::new();
    let mut pos = 0;
    while pos < mmap.len() {
        // Fast forward through timestamp (27 bytes + 1 space)
        if pos + 28 >= mmap.len() {
            break;
        }
        pos += 28;
        // Skip method
        while pos < mmap.len() && mmap[pos] != b' ' {
            pos += 1;
        }
        pos += 1; // skip space
        let ep_start = pos;
        while pos < mmap.len() && mmap[pos] != b' ' {
            pos += 1;
        }
        let ep_len = pos - ep_start;
        ep_table.get_or_insert(&mmap, ep_start, ep_len);
        // Skip rest of line
        while pos < mmap.len() && mmap[pos] != b'\n' {
            pos += 1;
        }
        pos += 1;
    }

    let num_endpoints = ep_table.endpoints.len();
    let num_groups = HOURS * num_endpoints;

    let num_threads = 4.min(
        thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4),
    );
    let chunk_size = mmap.len() / num_threads;

    let mut chunk_boundaries = vec![0; num_threads + 1];
    for t in 1..num_threads {
        let mut split = t * chunk_size;
        while split < mmap.len() && mmap[split] != b'\n' {
            split += 1;
        }
        if split < mmap.len() {
            split += 1;
        }
        chunk_boundaries[t] = split;
    }
    chunk_boundaries[num_threads] = mmap.len();

    // Pass 1: Count line occurrences and errors per (hour, ep) group
    let pass1_results = thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_threads);
        for t in 0..num_threads {
            let start = chunk_boundaries[t];
            let end = chunk_boundaries[t + 1];
            let ep_ref = &ep_table;
            let m_ref = &mmap[..];
            handles.push(s.spawn(move || {
                let mut counts = vec![0u32; num_groups];
                let mut errors = vec![0u32; num_groups];
                let mut p = start;
                while p < end {
                    if p + 28 >= end {
                        break;
                    }
                    let hour_idx = parse_hour_idx(&m_ref[p..p + 27]);
                    p += 28;
                    while p < end && m_ref[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let ep_start = p;
                    while p < end && m_ref[p] != b' ' {
                        p += 1;
                    }
                    let ep_len = p - ep_start;
                    let ep_id = ep_ref
                        .lookup(m_ref, &m_ref[ep_start..ep_start + ep_len])
                        .unwrap_or(0) as usize;
                    p += 1;
                    let is_err = m_ref[p] == b'5';
                    let gid = hour_idx * num_endpoints + ep_id;
                    counts[gid] += 1;
                    if is_err {
                        errors[gid] += 1;
                    }
                    while p < end && m_ref[p] != b'\n' {
                        p += 1;
                    }
                    p += 1;
                }
                (counts, errors)
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });

    let mut total_counts = vec![0u32; num_groups];
    let mut total_errors = vec![0u32; num_groups];
    for (t_counts, t_errors) in &pass1_results {
        for i in 0..num_groups {
            total_counts[i] += t_counts[i];
            total_errors[i] += t_errors[i];
        }
    }

    // Compute CSR offsets
    let mut group_offsets = vec![0usize; num_groups + 1];
    let mut running_sum = 0usize;
    for i in 0..num_groups {
        group_offsets[i] = running_sum;
        running_sum += total_counts[i] as usize;
    }
    group_offsets[num_groups] = running_sum;
    let total_records = running_sum;

    // Per-thread write offsets
    let mut thread_write_offsets = vec![vec![0usize; num_groups]; num_threads];
    let mut current_pos = group_offsets[..num_groups].to_vec();
    for t in 0..num_threads {
        for g in 0..num_groups {
            thread_write_offsets[t][g] = current_pos[g];
            current_pos[g] += pass1_results[t].0[g] as usize;
        }
    }

    // Allocate single contiguous latency arena
    let mut latencies = vec![0u32; total_records];
    let lat_ptr = latencies.as_mut_ptr() as usize;

    // Pass 2: Concurrently populate latencies into CSR slices
    thread::scope(|s| {
        for t in 0..num_threads {
            let start = chunk_boundaries[t];
            let end = chunk_boundaries[t + 1];
            let ep_ref = &ep_table;
            let m_ref = &mmap[..];
            let mut write_offsets = thread_write_offsets[t].clone();
            s.spawn(move || {
                let lat_base = lat_ptr as *mut u32;
                let mut p = start;
                while p < end {
                    if p + 28 >= end {
                        break;
                    }
                    let hour_idx = parse_hour_idx(&m_ref[p..p + 27]);
                    p += 28;
                    while p < end && m_ref[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let ep_start = p;
                    while p < end && m_ref[p] != b' ' {
                        p += 1;
                    }
                    let ep_len = p - ep_start;
                    let ep_id = ep_ref
                        .lookup(m_ref, &m_ref[ep_start..ep_start + ep_len])
                        .unwrap_or(0) as usize;
                    p += 1;
                    // skip status
                    while p < end && m_ref[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let lat_start = p;
                    while p < end && m_ref[p] != b'\n' {
                        p += 1;
                    }
                    let lat = parse_u32(&m_ref[lat_start..p]);
                    p += 1;

                    let gid = hour_idx * num_endpoints + ep_id;
                    let slot = write_offsets[gid];
                    write_offsets[gid] += 1;
                    unsafe {
                        *lat_base.add(slot) = lat;
                    }
                }
            });
        }
    });

    // Step 3: Sort endpoints by byte-order
    let mut sorted_endpoints: Vec<u16> = (0..num_endpoints as u16).collect();
    sorted_endpoints.sort_unstable_by(|&a, &b| {
        let (oa, la) = ep_table.endpoints[a as usize];
        let (ob, lb) = ep_table.endpoints[b as usize];
        mmap[oa..oa + la].cmp(&mmap[ob..ob + lb])
    });

    // Step 4: Quantile selection & formatted line generation per hour
    let mut out_file = File::create(&out_path).unwrap();
    let mut out_buf = Vec::with_capacity(1024 * 1024);

    for hour_idx in 0..HOURS {
        let hour_str = HOUR_STRINGS[hour_idx];
        for &ep_id in &sorted_endpoints {
            let gid = hour_idx * num_endpoints + ep_id as usize;
            let cnt = total_counts[gid] as usize;
            if cnt == 0 {
                continue;
            }
            let start = group_offsets[gid];
            let end = group_offsets[gid + 1];
            let group_lats = &mut latencies[start..end];

            let (p50, p95, p99) = if cnt == 1 {
                (group_lats[0], group_lats[0], group_lats[0])
            } else if cnt <= 32 {
                group_lats.sort_unstable();
                let r50 = (50 * cnt + 99) / 100 - 1;
                let r95 = (95 * cnt + 99) / 100 - 1;
                let r99 = (99 * cnt + 99) / 100 - 1;
                (group_lats[r50], group_lats[r95], group_lats[r99])
            } else {
                let r50 = (50 * cnt + 99) / 100 - 1;
                let r95 = (95 * cnt + 99) / 100 - 1;
                let r99 = (99 * cnt + 99) / 100 - 1;
                group_lats.select_nth_unstable(r99);
                let val_99 = group_lats[r99];
                group_lats[..r99].select_nth_unstable(r95);
                let val_95 = group_lats[r95];
                group_lats[..r95].select_nth_unstable(r50);
                let val_50 = group_lats[r50];
                (val_50, val_95, val_99)
            };

            let errs = total_errors[gid];
            let ppm = (errs as u64 * 1000000) / (cnt as u64);
            let (oa, la) = ep_table.endpoints[ep_id as usize];
            let ep_bytes = &mmap[oa..oa + la];

            // hour endpoint count p50 p95 p99 errors error_ppm
            out_buf.extend_from_slice(hour_str.as_bytes());
            out_buf.push(b' ');
            out_buf.extend_from_slice(ep_bytes);
            out_buf.push(b' ');
            itoa(&mut out_buf, cnt as u64);
            out_buf.push(b' ');
            itoa(&mut out_buf, p50 as u64);
            out_buf.push(b' ');
            itoa(&mut out_buf, p95 as u64);
            out_buf.push(b' ');
            itoa(&mut out_buf, p99 as u64);
            out_buf.push(b' ');
            itoa(&mut out_buf, errs as u64);
            out_buf.push(b' ');
            itoa(&mut out_buf, ppm);
            out_buf.push(b'\n');

            if out_buf.len() >= 512 * 1024 {
                out_file.write_all(&out_buf).unwrap();
                out_buf.clear();
            }
        }
    }
    if !out_buf.is_empty() {
        out_file.write_all(&out_buf).unwrap();
    }
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
    // Fallback for Windows local test harness
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
