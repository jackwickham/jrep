use std::io::prelude::*;
use std::io::ErrorKind;
use std::io::Result;
use std::thread;
use std::sync::mpsc;
use crate::pattern;

type SkipTable = [usize; 256];
const BUFFER_SIZE: usize = 2 << 18; // 260k
const READ_SIZE: usize = 2 << 16; // 65k

/// A macro similar to `vec![$elem; $size]` which returns a boxed array.
///
/// ```rustc
///     let _: Box<[u8; 1024]> = box_array![0; 1024];
/// ```
/// https://stackoverflow.com/a/68122278/2826188
macro_rules! box_array {
    ($val:expr ; $len:expr) => {{
        // Use a generic function so that the pointer cast remains type-safe
        fn vec_to_boxed_array<T>(vec: Vec<T>) -> Box<[T; $len]> {
            let boxed_slice = vec.into_boxed_slice();

            let ptr = ::std::boxed::Box::into_raw(boxed_slice) as *mut [T; $len];

            unsafe { Box::from_raw(ptr) }
        }

        vec_to_boxed_array(vec![$val; $len])
    }};
}

pub fn search_file<R : 'static + Read + std::marker::Send>(file: R, pattern_str: &str) -> Result<Vec<String>> {
    let pattern = pattern::Pattern::parse(pattern_str).map_err(|e| std::io::Error::new(ErrorKind::Other, e))?;
    let skip_table = build_skip_table(&pattern);
    let mut buffer = FileBuffer::new(file);
    buffer.advance(pattern.len() - 1);
    let mut matches = Vec::new();

    while let Some(c) = buffer.read()? {
        let skip_distance = skip_table[c as usize];
        if skip_distance == 0 {
            if check_match(&buffer, &pattern) {
                matches.push(find_line_match(&mut buffer, &pattern)?);
            } else {
                buffer.advance(1);
            }
        } else {
            buffer.advance(skip_distance);
        }
    }
    return Ok(matches);
}

fn build_skip_table(pattern: &pattern::Pattern) -> SkipTable {
    let mut skip_distance = pattern.len();
    let mut table = [skip_distance; 256];

    for pattern_char in pattern.chars() {
        skip_distance -= 1;
        for c in pattern_char.all_chars() {
            table[c as usize] = skip_distance;
        }
    }

    table
}

fn check_match(buffer: &FileBuffer, pattern: &pattern::Pattern) -> bool {
    let mut pattern_it = pattern.chars().iter().rev().zip(0..);
    pattern_it.next();
    for (matcher, offset) in &mut pattern_it {
        if !matcher.matches(buffer.read_back(offset).unwrap()) {
            return false;
        }
    }
    true
}

fn find_line_match(buffer: &mut FileBuffer, pattern: &pattern::Pattern) -> Result<String> {
    let mut back_offset = 0;
    for offset in pattern.len().. {
        match buffer.read_back(offset) {
            None => {
                back_offset = offset - 1;
                break;
            }
            Some(b'\n') => {
                back_offset = offset - 1;
                break;
            },
            _ => {}
        };
    }
    let read_back = buffer.read_back_bulk(back_offset);
    
    let mut raw_result = read_back.0.to_vec();
    raw_result.extend_from_slice(read_back.1);

    buffer.advance(1);
    while let Some(c) = buffer.read()? {
        if c == b'\n' {
            break;
        }
        raw_result.push(c);
        buffer.advance(1);
    }

    Ok(String::from(String::from_utf8_lossy(&raw_result)))
}

struct FileBuffer {
    buf: Box<[u8; 2 << 18]>,
    offset: usize,
    forward_read_bound: usize,
    current_read_start: usize,
    read_reserved_end: usize,
    high_water_mark: usize,
    channel_write: mpsc::Sender<ReadRequest>,
    channel_read: mpsc::Receiver<Result<ReadResult>>,
    eof: bool,
}

impl FileBuffer {
    pub fn new<R : 'static + Read + std::marker::Send>(file: R) -> FileBuffer {

        let (req_tx, req_rx) = mpsc::channel();
        let (res_tx, res_rx) = mpsc::channel();

        thread::spawn(move || {
            unsafe {
                run_read_thread(file, req_rx, res_tx);
            }
        });

        let mut buf = FileBuffer{
            buf: box_array![0; BUFFER_SIZE],
            offset: 0,
            forward_read_bound: 0,
            current_read_start: 0,
            read_reserved_end: 0,
            high_water_mark: 0,
            channel_write: req_tx,
            channel_read: res_rx,
            eof: false,
        };

        buf.trigger_read();

        buf
    }

    fn read(&mut self) -> Result<Option<u8>> {
        while self.offset >= self.forward_read_bound {
            if !self.read_file()? {
                return Ok(None)
            }
        }

        return Ok(Some(self.buf[self.offset]));
    }

    fn read_back(&self, distance: usize) -> Option<u8> {
        if self.offset < distance {
            if self.high_water_mark > 0 {
                if distance - self.offset > self.high_water_mark - self.read_reserved_end {
                    panic!("Cannot read back any further (distance={}, high water mark={})", distance, self.high_water_mark);
                }
                Some(self.buf[self.offset + self.high_water_mark - distance])
            } else {
                // Start of file
                None
            }
        } else {
            Some(self.buf[self.offset - distance])
        }
    }

    fn read_back_bulk(&self, backtrack_distance: usize) -> (&[u8], &[u8]) {
        if self.offset < backtrack_distance {
            (&self.buf[(self.offset + self.high_water_mark - backtrack_distance)..self.high_water_mark], &self.buf[0..=self.offset])
        } else {
            (&self.buf[(self.offset - backtrack_distance)..=self.offset], &[])
        }
    }

    fn advance(&mut self, distance: usize)  {
        self.offset += distance;
    }

    fn read_file(&mut self) -> Result<bool> {
        if self.eof {
            return Ok(false);
        }

        // Wait for the previous read to finish
        let read_result = self.channel_read.recv().unwrap()?;

        // Expand readable region
        if self.current_read_start == 0 {
            self.offset -= self.high_water_mark;
        }
        self.forward_read_bound = self.current_read_start + read_result.bytes_read;

        if read_result.eof {
            self.eof = true;
            return Ok(false);
        } else {
            self.trigger_read();
            return Ok(true);
        }
    }

    fn trigger_read(&mut self) {
        if self.forward_read_bound + READ_SIZE > BUFFER_SIZE {
            self.current_read_start = 0;
            self.read_reserved_end = READ_SIZE;
            self.high_water_mark = self.forward_read_bound;
        } else {
            self.current_read_start = self.forward_read_bound;
            self.read_reserved_end = self.forward_read_bound + READ_SIZE;
        }

        let result = self.channel_write.send(ReadRequest{
            target: &mut self.buf[self.current_read_start..self.read_reserved_end],
        });
        match result {
            Ok(_) => {},
            Err(e) => {
                println!("{:?}", e);
                panic!("Failed to send: {:?}", e);
            }
        }
    }
}

struct ReadRequest {
    target: *mut [u8],
}

unsafe impl Send for ReadRequest {}

struct ReadResult {
    bytes_read: usize,
    eof: bool,
}


unsafe fn run_read_thread<R : Read>(mut file: R, channel_read: mpsc::Receiver<ReadRequest>, channel_write: mpsc::Sender<Result<ReadResult>>) {
    while let Ok(msg) = channel_read.recv() {
        let buffer: &mut [u8] = &mut *msg.target;
        match file.read(buffer) {
            Ok(len) => {
                let read_result = ReadResult{ bytes_read: len, eof: len == 0 };
                channel_write.send(Ok(read_result)).unwrap();
                if len == 0 {
                    return;
                }
            },
            Err(ref e) if e.kind() == ErrorKind::Interrupted => {
                channel_write.send(Ok(ReadResult{ bytes_read: 0, eof: false })).unwrap();
            },
            Err(e) => {
                channel_write.send(Err(e)).unwrap();
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    const NO_MATCH: Vec<String> = vec![];

    #[test]
    fn test_match() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "bar").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_no_match() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "far").unwrap(), NO_MATCH);
    }

    #[test]
    fn test_match_at_start() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "foo").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_match_at_end() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "baz").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_match_after_backtrack() {
        assert_eq!(search_file("ooooffoo".as_bytes(), "foo").unwrap(), vec!["ooooffoo"]);
    }

    #[test]
    fn test_no_match_underflow() {
        assert_eq!(search_file("ffffff".as_bytes(), "\0f").unwrap(), NO_MATCH);
    }

    #[test]
    fn test_match_wildcard() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "b.r").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_match_wildcard_at_end() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "ba.").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_match_range() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "b[cab]r").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_no_match_incorrect_range() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "b[cd]r").unwrap(), NO_MATCH);
    }

    #[test]
    fn test_match_negated_range() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "b[^cd]r").unwrap(), vec!["foo bar baz"]);
    }

    #[test]
    fn test_no_match_incorrect_negated_range() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "b[^ab]r").unwrap(), NO_MATCH);
    }

    #[test]
    fn test_outputs_matching_lines() {
        assert_eq!(search_file("foo foo\nfoo\nbar baz\nfoo bar".as_bytes(), "foo").unwrap(), vec!["foo foo", "foo", "foo bar"]);
    }

    #[test]
    fn test_match_split_read() {
        assert_eq!(search_file(MockReader::new_ok(&["01234", "56789", ""]), "345").unwrap(), vec!["0123456789"]);
    }

    #[test]
    fn test_reads_until_eof() {
        let reader = MockReader::new_ok(&["foo", "bar", ""]);
        assert_eq!(search_file(reader, "baz").unwrap(), NO_MATCH);
    }

    #[test]
    fn test_retries_interrupted() {
        let reader = MockReader::new(vec![Ok("foo"), Err(std::io::Error::new(ErrorKind::Interrupted, "Interrupted")), Ok("bar"), Ok("")]);
        assert_eq!(search_file(reader, "bar").unwrap(), vec!["foobar"]);
    }

    #[test]
    fn test_propagates_errors() {
        let reader = MockReader::new(vec![Ok("foo"), Err(std::io::Error::new(ErrorKind::BrokenPipe, "Broken"))]);
        assert_eq!(search_file(reader, "b").unwrap_err().kind(), ErrorKind::BrokenPipe);
    }

    #[test]
    fn test_wraparound() {
        let mut data = vec![vec![0; READ_SIZE], vec![1; READ_SIZE], vec![2; READ_SIZE], vec![3; READ_SIZE], vec![4; READ_SIZE]];
        data[3][READ_SIZE - 2] = b'\n';
        data[3][READ_SIZE - 1] = b'a';
        data[4][0] = b'b';
        data[4][1] = b'\n';
        let reader = MockReader::new_bytes(data);
        assert_eq!(search_file(reader, "ab").unwrap(), vec!["ab"]);
    }

    struct MockReader {
        results: Vec<Result<Vec<u8>>>
    }

    impl MockReader {
        fn new(results: Vec<Result<&str>>) -> MockReader {
            let actual_results = results.into_iter()
                    .rev()
                    .map(|r| r.map(|e| e.as_bytes().into()))
                    .collect();
            MockReader{
                results: actual_results
            }
        }

        fn new_ok(results: &[&str]) -> MockReader {
            let actual_results = results.into_iter()
                    .rev()
                    .map(|e| Ok(e.as_bytes().into()))
                    .collect();
            MockReader{
                results: actual_results
            }
        }

        fn new_bytes(results: Vec<Vec<u8>>) -> MockReader {
            let actual_results = results.into_iter()
                    .rev()
                    .map(|e| Ok(e))
                    .collect();
            MockReader{
                results: actual_results
            }
        }
    }

    impl Read for MockReader {
        fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
            let res = self.results.pop().unwrap_or(Ok(vec![]))?;
            buf[0..res.len()].copy_from_slice(&res);
            Ok(res.len())
        }
    }

    impl Drop for MockReader {
        fn drop(&mut self) {
            assert_eq!(self.results.len(), 0);
        }
    }
}
