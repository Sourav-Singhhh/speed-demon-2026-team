use std::collections::HashMap;
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::Write as IoWrite;
use std::path::Path;

const BOM: &[u8] = b"\xEF\xBB\xBF";
const UNMATCHED_SENTINEL: u32 = u32::MAX;

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
        let mut pos = 0;
        if data.starts_with(BOM) {
            pos += 3;
        }
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
    table: Vec<u32>,
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

        let mut table = vec![UNMATCHED_SENTINEL; max_region_id + 1];
        for (rid, c_idx) in raw_regions {
            table[rid] = c_idx as u32;
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
        if rid < self.table.len() {
            let idx = self.table[rid];
            if idx == UNMATCHED_SENTINEL {
                self.unmatched_idx
            } else {
                idx as usize
            }
        } else {
            self.unmatched_idx
        }
    }
}

pub struct NamePool {
    map: HashMap<Vec<u8>, u32>,
}

impl NamePool {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn intern(&mut self, name: &[u8]) -> u32 {
        if let Some(&id) = self.map.get(name) {
            id
        } else {
            let id = self.map.len() as u32;
            self.map.insert(name.to_vec(), id);
            id
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
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
        self.seen_names.iter().map(|&w| w.count_ones() as u64).sum()
    }

    pub fn format_line(&self, out: &mut String) {
        let code_str = std::str::from_utf8(&self.code).unwrap_or("_UNMATCHED");
        write!(
            out,
            "{} {} {} ",
            code_str,
            self.count,
            self.id_sum
        ).unwrap();
        format_cents_into(self.amount_sum, out);
        out.push(' ');
        format_cents_into(self.amount_min.unwrap_or(0), out);
        out.push(' ');
        format_cents_into(self.amount_max.unwrap_or(0), out);
        write!(
            out,
            " {} {} {}\n",
            self.distinct_names_count(),
            self.name_bytes,
            self.note_bytes
        ).unwrap();
    }
}

pub fn execute_join(records_data: &[u8], regions_data: &[u8]) -> Result<Vec<u8>, String> {
    let region_table = RegionTable::from_bytes(regions_data)?;
    let mut country_aggs: Vec<CountryAccumulator> = region_table
        .countries
        .iter()
        .map(|code| CountryAccumulator::new(code.clone()))
        .collect();

    let mut name_pool = NamePool::new();
    let mut parser = RecordParser::new(records_data)?;

    parser.next_record(|id, name_slice, name_bytes, note_bytes, region_id, cents| {
        let country_idx = region_table.lookup(region_id);
        let name_id = name_pool.intern(name_slice);
        country_aggs[country_idx].add(id, name_id, name_bytes, note_bytes, cents);
        Ok(())
    })?;

    // Filter countries with count > 0 and sort bytewise ascending
    let mut active_countries: Vec<&CountryAccumulator> = country_aggs.iter().filter(|c| c.count > 0).collect();
    active_countries.sort_by(|a, b| a.code.cmp(&b.code));

    let mut output = String::with_capacity(active_countries.len() * 80);
    for country in active_countries {
        country.format_line(&mut output);
    }

    Ok(output.into_bytes())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let data_dir = if args.len() > 1 { &args[1] } else { "/data" };
    let out_dir = if args.len() > 2 { &args[2] } else { "/out" };

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
    let records_data = fs::read(&records_path).expect("failed to read records.csv");

    let output_bytes = execute_join(&records_data, &regions_data).expect("join execution failed");

    let out_dir_path = Path::new(out_dir);
    fs::create_dir_all(out_dir_path).expect("failed to create output directory");
    let out_file_path = out_dir_path.join("aggregates.txt");

    let mut file = fs::File::create(&out_file_path).expect("failed to create aggregates.txt");
    file.write_all(&output_bytes).expect("failed to write aggregates.txt");
    file.flush().expect("failed to flush aggregates.txt");

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
        // Test near i64::MIN and i64::MAX (no overflow)
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
        // Exact format: "USA 1 1 10.50 10.50 10.50 1 5 4\n"
        assert_eq!(out, b"USA 1 1 10.50 10.50 10.50 1 5 4\n");
        assert!(out.ends_with(b"\n"));
        assert!(!out.ends_with(b"\r\n"));
        // Check single space separation
        let line = std::str::from_utf8(&out).unwrap();
        let parts: Vec<&str> = line.trim_end_matches('\n').split(' ').collect();
        assert_eq!(parts.len(), 9);
        assert_eq!(parts, vec!["USA", "1", "1", "10.50", "10.50", "10.50", "1", "5", "4"]);
    }
}
