use std::env;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;

const HOURS_COUNT: usize = 72;

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

#[inline(always)]
fn parse_hour_idx(ts: &[u8]) -> usize {
    let day = (ts[8] - b'0') * 10 + (ts[9] - b'0');
    let day_offset = if ts[6] == b'0' { (day - 30) as usize } else { (day + 1) as usize };
    let hour = ((ts[11] - b'0') * 10 + (ts[12] - b'0')) as usize;
    (day_offset * 24 + hour) - 18
}

#[inline(always)]
fn fast_hash(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for &b in bytes {
        h = (h ^ (b as u64)).wrapping_mul(0x100000001b3);
    }
    h
}

const HASH_TABLE_SIZE: usize = 4096;
const HASH_MASK: usize = HASH_TABLE_SIZE - 1;

struct FastCatalog {
    keys: Vec<Vec<u8>>,
    table_hashes: [u64; HASH_TABLE_SIZE],
    table_ids: [u16; HASH_TABLE_SIZE],
}

impl FastCatalog {
    fn new(sorted_endpoints: Vec<Vec<u8>>) -> Self {
        let mut table_hashes = [0u64; HASH_TABLE_SIZE];
        let mut table_ids = [0xffffu16; HASH_TABLE_SIZE];

        for (id, ep) in sorted_endpoints.iter().enumerate() {
            let h = fast_hash(ep);
            let mut slot = (h as usize) & HASH_MASK;
            while table_ids[slot] != 0xffff {
                slot = (slot + 1) & HASH_MASK;
            }
            table_hashes[slot] = h;
            table_ids[slot] = id as u16;
        }

        Self {
            keys: sorted_endpoints,
            table_hashes,
            table_ids,
        }
    }

    #[inline(always)]
    fn get_id(&self, ep: &[u8]) -> usize {
        let h = fast_hash(ep);
        let mut slot = (h as usize) & HASH_MASK;
        loop {
            let id = self.table_ids[slot];
            if id != 0xffff && self.table_hashes[slot] == h && self.keys[id as usize] == ep {
                return id as usize;
            }
            slot = (slot + 1) & HASH_MASK;
        }
    }
}

fn partition_input(data: &[u8], num_parts: usize) -> Vec<&[u8]> {
    let mut chunks = Vec::with_capacity(num_parts);
    let chunk_size = data.len() / num_parts;
    let mut start = 0;

    for i in 0..num_parts {
        if start >= data.len() {
            break;
        }
        if i == num_parts - 1 {
            chunks.push(&data[start..]);
            break;
        }
        let mut end = (start + chunk_size).min(data.len());
        while end < data.len() && data[end] != b'\n' {
            end += 1;
        }
        if end < data.len() && data[end] == b'\n' {
            end += 1;
        }
        chunks.push(&data[start..end]);
        start = end;
    }
    chunks
}

#[inline(always)]
fn write_u32(buf: &mut Vec<u8>, mut n: u32) {
    if n == 0 {
        buf.push(b'0');
        return;
    }
    let mut temp = [0u8; 10];
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create out dir");
    let out_file_path = out_dir_path.join("summary.txt");

    let input_path = Path::new(data_dir).join("requests.log");
    let file = fs::File::open(&input_path).expect("open requests.log failed");
    let meta = file.metadata().expect("stat failed");
    let file_len = meta.len() as usize;

    if file_len == 0 {
        fs::write(&out_file_path, b"").expect("write empty summary failed");
        return;
    }

    let input_data: &[u8] = if let Ok(mapped) = mmap_file(&file, file_len) {
        mapped
    } else {
        Box::leak(fs::read(&input_path).expect("read requests.log failed").into_boxed_slice())
    };

    let mut precomputed_hours = Vec::with_capacity(HOURS_COUNT);
    for (m, d, h0, h1) in [(10, 30, 18, 24), (10, 31, 0, 24), (11, 1, 0, 24), (11, 2, 0, 18)] {
        for h in h0..h1 {
            precomputed_hours.push(format!("2026-{m:02}-{d:02}T{h:02}:00:00Z"));
        }
    }

    let num_threads = env::var("RAYON_NUM_THREADS")
        .or_else(|_| env::var("THREADS"))
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8));

    let chunks = partition_input(input_data, num_threads.max(1));

    // Phase 1: Collect distinct endpoints across chunks
    let local_catalogs: Vec<Vec<Vec<u8>>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in &chunks {
            handles.push(s.spawn(move || {
                let mut endpoints: Vec<Vec<u8>> = Vec::with_capacity(2048);
                let mut pos = 0;
                while pos < chunk.len() {
                    let line_start = pos;
                    while pos < chunk.len() && chunk[pos] != b'\n' {
                        pos += 1;
                    }
                    let line = &chunk[line_start..pos];
                    if pos < chunk.len() && chunk[pos] == b'\n' {
                        pos += 1;
                    }
                    if line.len() < 32 {
                        continue;
                    }
                    let mut p = 31;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let ep_start = p;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    let ep = &line[ep_start..p];
                    if !endpoints.iter().any(|existing| existing.as_slice() == ep) {
                        endpoints.push(ep.to_vec());
                    }
                }
                endpoints
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut all_endpoints = Vec::with_capacity(2048);
    for list in local_catalogs {
        for ep in list {
            if !all_endpoints.iter().any(|existing| existing == &ep) {
                all_endpoints.push(ep);
            }
        }
    }
    all_endpoints.sort_unstable();
    let catalog = FastCatalog::new(all_endpoints);

    let num_endpoints = catalog.keys.len();
    let total_groups = HOURS_COUNT * num_endpoints;

    // Phase 2: Parallel line count per group
    struct ChunkStats {
        group_counts: Vec<u32>,
        group_errors: Vec<u32>,
    }

    let chunk_stats: Vec<ChunkStats> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in &chunks {
            let cat = &catalog;
            handles.push(s.spawn(move || {
                let mut group_counts = vec![0u32; total_groups];
                let mut group_errors = vec![0u32; total_groups];
                let mut pos = 0;
                while pos < chunk.len() {
                    let line_start = pos;
                    while pos < chunk.len() && chunk[pos] != b'\n' {
                        pos += 1;
                    }
                    let line = &chunk[line_start..pos];
                    if pos < chunk.len() && chunk[pos] == b'\n' {
                        pos += 1;
                    }
                    if line.len() < 32 {
                        continue;
                    }
                    let hour_idx = parse_hour_idx(&line[0..27]);
                    let mut p = 31;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let ep_start = p;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    let ep_id = cat.get_id(&line[ep_start..p]);
                    let group_id = hour_idx * num_endpoints + ep_id;

                    group_counts[group_id] += 1;
                    p += 1;
                    if line[p] == b'5' {
                        group_errors[group_id] += 1;
                    }
                }
                ChunkStats {
                    group_counts,
                    group_errors,
                }
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut total_group_counts = vec![0u32; total_groups];
    let mut total_group_errors = vec![0u32; total_groups];
    let mut chunk_write_offsets: Vec<Vec<u32>> = Vec::with_capacity(chunks.len());
    for _ in 0..chunks.len() {
        chunk_write_offsets.push(vec![0u32; total_groups]);
    }

    let mut running_group_offsets = vec![0u32; total_groups];
    for (c_idx, stats) in chunk_stats.iter().enumerate() {
        for g in 0..total_groups {
            chunk_write_offsets[c_idx][g] = running_group_offsets[g];
            running_group_offsets[g] += stats.group_counts[g];
            total_group_counts[g] += stats.group_counts[g];
            total_group_errors[g] += stats.group_errors[g];
        }
    }

    let mut group_offsets = vec![0u32; total_groups + 1];
    let mut total_requests = 0usize;
    for g in 0..total_groups {
        group_offsets[g] = total_requests as u32;
        total_requests += total_group_counts[g] as usize;
    }
    group_offsets[total_groups] = total_requests as u32;

    for c_idx in 0..chunks.len() {
        for g in 0..total_groups {
            chunk_write_offsets[c_idx][g] += group_offsets[g];
        }
    }

    // Phase 3: Populate all_latencies directly into CSR
    let mut all_latencies = vec![0u32; total_requests];
    let latencies_ptr = all_latencies.as_mut_ptr() as usize;

    std::thread::scope(|s| {
        for (c_idx, chunk) in chunks.iter().enumerate() {
            let cat = &catalog;
            let mut write_offsets = chunk_write_offsets[c_idx].clone();
            s.spawn(move || {
                let ptr = latencies_ptr as *mut u32;
                let mut pos = 0;
                while pos < chunk.len() {
                    let line_start = pos;
                    while pos < chunk.len() && chunk[pos] != b'\n' {
                        pos += 1;
                    }
                    let line = &chunk[line_start..pos];
                    if pos < chunk.len() && chunk[pos] == b'\n' {
                        pos += 1;
                    }
                    if line.len() < 32 {
                        continue;
                    }
                    let hour_idx = parse_hour_idx(&line[0..27]);
                    let mut p = 31;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    p += 1;
                    let ep_start = p;
                    while p < line.len() && line[p] != b' ' {
                        p += 1;
                    }
                    let ep_id = cat.get_id(&line[ep_start..p]);
                    let group_id = hour_idx * num_endpoints + ep_id;

                    p += 1; // start of status
                    p += 4; // skip status (3 digits) + space
                    let mut latency = 0u32;
                    while p < line.len() && line[p] >= b'0' && line[p] <= b'9' {
                        latency = latency * 10 + (line[p] - b'0') as u32;
                        p += 1;
                    }

                    let dst = write_offsets[group_id];
                    write_offsets[group_id] += 1;
                    unsafe {
                        *ptr.add(dst as usize) = latency;
                    }
                }
            });
        }
    });

    // Phase 4: Sort each group's latencies in parallel
    let latencies_slice = all_latencies.as_mut_slice();
    std::thread::scope(|s| {
        let groups_per_thread = (total_groups + num_threads - 1) / num_threads;
        for t in 0..num_threads {
            let g_start = (t * groups_per_thread).min(total_groups);
            let g_end = ((t + 1) * groups_per_thread).min(total_groups);
            if g_start >= g_end {
                continue;
            }
            let offsets_ref = &group_offsets;
            let slice_ptr = latencies_slice.as_mut_ptr() as usize;
            s.spawn(move || {
                let base = slice_ptr as *mut u32;
                for g in g_start..g_end {
                    let start = offsets_ref[g] as usize;
                    let end = offsets_ref[g + 1] as usize;
                    if end > start {
                        let sub_slice = unsafe {
                            std::slice::from_raw_parts_mut(base.add(start), end - start)
                        };
                        sub_slice.sort_unstable();
                    }
                }
            });
        }
    });

    // Phase 5: Parallel output formatting by hour ranges
    let hours_per_thread = (HOURS_COUNT + num_threads - 1) / num_threads;
    let formatted_chunks: Vec<Vec<u8>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_threads);
        for t in 0..num_threads {
            let h_start = (t * hours_per_thread).min(HOURS_COUNT);
            let h_end = ((t + 1) * hours_per_thread).min(HOURS_COUNT);
            if h_start >= h_end {
                continue;
            }
            let cat = &catalog;
            let counts = &total_group_counts;
            let errs = &total_group_errors;
            let offsets = &group_offsets;
            let vals = &latencies_slice;
            let hours_ref = &precomputed_hours;

            handles.push(s.spawn(move || {
                let mut chunk_buf = Vec::with_capacity(2 * 1024 * 1024);
                for h in h_start..h_end {
                    let hour_bytes = hours_ref[h].as_bytes();
                    for ep_id in 0..num_endpoints {
                        let group_id = h * num_endpoints + ep_id;
                        let count = counts[group_id] as usize;
                        if count == 0 {
                            continue;
                        }
                        let start = offsets[group_id] as usize;
                        let end = offsets[group_id + 1] as usize;
                        let g_vals = &vals[start..end];

                        let r50 = (50 * count + 99) / 100 - 1;
                        let r95 = (95 * count + 99) / 100 - 1;
                        let r99 = (99 * count + 99) / 100 - 1;
                        let p50 = g_vals[r50];
                        let p95 = g_vals[r95];
                        let p99 = g_vals[r99];
                        let e_count = errs[group_id] as usize;
                        let ppm = ((e_count as u64 * 1_000_000) / count as u64) as u32;

                        chunk_buf.extend_from_slice(hour_bytes);
                        chunk_buf.push(b' ');
                        chunk_buf.extend_from_slice(&cat.keys[ep_id]);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, count as u32);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, p50);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, p95);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, p99);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, e_count as u32);
                        chunk_buf.push(b' ');
                        write_u32(&mut chunk_buf, ppm);
                        chunk_buf.push(b'\n');
                    }
                }
                chunk_buf
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut out_file = fs::File::create(&out_file_path).expect("failed to create summary.txt");
    for chunk in formatted_chunks {
        out_file.write_all(&chunk).expect("failed to write chunk");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hour_idx() {
        assert_eq!(parse_hour_idx(b"2026-10-30T18:00:00.000000Z"), 0);
        assert_eq!(parse_hour_idx(b"2026-10-30T23:59:59.999999Z"), 5);
        assert_eq!(parse_hour_idx(b"2026-10-31T00:00:00.000000Z"), 6);
        assert_eq!(parse_hour_idx(b"2026-11-01T00:00:00.000000Z"), 30);
        assert_eq!(parse_hour_idx(b"2026-11-02T17:59:59.999999Z"), 71);
    }
}
