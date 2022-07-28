use std::io::prelude::*;
use std::fs::File;
use std::io::ErrorKind;
use std::io::Result;

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

fn main() {
    let mut args = std::env::args();

    args.next();
    let pattern = args.next().unwrap();
    let file_path = args.next().unwrap();

    if pattern.len() == 0 {
        panic!("A pattern must be provided");
    }
    // We need enough space left in the buffer to read the whole match and backtrack
    if pattern.len() > READ_SIZE {
        panic!("Pattern too long");
    }

    let file = File::open(file_path).unwrap();

    if search_file(file, &pattern).unwrap() {
        std::process::exit(0);
    } else {
        std::process::exit(1);
    }
}

fn search_file<R : Read>(file: R, pattern: &str) -> Result<bool> {
    let skip_table = build_skip_table(pattern);
    let mut buffer = FileBuffer::new(file);
    buffer.advance(pattern.len() - 1);

    while let Some(c) = buffer.read()? {
        let skip_distance = skip_table[c as usize];
        if skip_distance == 0 {
            if check_match(&buffer, pattern) {
                return Ok(true);
            } else {
                buffer.advance(1);
            }
        } else {
            buffer.advance(skip_distance);
        }
    }
    return Ok(false);
}

fn build_skip_table(pattern: &str) -> SkipTable {
    let mut skip_distance = pattern.len();
    let mut table = [skip_distance; 256];

    for c in pattern.bytes() {
        skip_distance -= 1;
        table[c as usize] = skip_distance;
    }

    table
}

fn check_match<R : Read>(buffer: &FileBuffer<R>, pattern: &str) -> bool {
    let mut pattern_it = pattern.bytes().rev().zip(0..);
    pattern_it.next();
    for (expected, offset) in &mut pattern_it {
        if buffer.read_back(offset) != expected {
            return false;
        }
    }
    true
}

struct FileBuffer<R : Read> {
    buf: Box<[u8; 2 << 18]>,
    file: R,
    offset: usize,
    next_available_index: usize,
    high_water_mark: usize,
}

impl <R : Read> FileBuffer<R> {
    pub fn new(file: R) -> FileBuffer<R> {
        FileBuffer{
            buf: box_array![0; BUFFER_SIZE],
            file,
            offset: 0,
            next_available_index: 0,
            high_water_mark: 0,
        }
    }

    fn read(&mut self) -> Result<Option<u8>> {
        while self.offset >= self.next_available_index {
            if !self.read_file()? {
                return Ok(None)
            }
        }

        return Ok(Some(self.buf[self.offset]));
    }

    fn read_back(&self, distance: usize) -> u8 {
        if self.offset < distance {
            self.buf[self.offset + self.high_water_mark - distance]
        } else {
            self.buf[self.offset - distance]
        }
    }

    fn advance(&mut self, distance: usize)  {
        self.offset += distance;
    }

    fn read_file(&mut self) -> Result<bool> {
        if self.next_available_index > BUFFER_SIZE - READ_SIZE {
            // wrap around
            self.offset -= self.next_available_index;
            self.high_water_mark = self.next_available_index;
            self.next_available_index = 0;
        }
        match self.file.read(&mut self.buf[(self.next_available_index)..(self.next_available_index + READ_SIZE)]) {
            Ok(len) => {
                self.next_available_index += len;
                Ok(len > 0)
            },
            Err(ref e) if e.kind() == ErrorKind::Interrupted => Ok(true),
            Err(e) => Err(e),
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "bar").unwrap(), true);
    }

    #[test]
    fn test_no_match() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "far").unwrap(), false);
    }

    #[test]
    fn test_match_at_start() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "foo").unwrap(), true);
    }

    #[test]
    fn test_match_at_end() {
        assert_eq!(search_file("foo bar baz".as_bytes(), "baz").unwrap(), true);
    }

    #[test]
    fn test_match_after_backtrack() {
        assert_eq!(search_file("ooooffoo".as_bytes(), "foo").unwrap(), true);
    }

    #[test]
    fn test_no_match_underflow() {
        assert_eq!(search_file("ffffff".as_bytes(), "\0f").unwrap(), false);
    }

    #[test]
    fn test_match_split_read() {
        assert_eq!(search_file(MockReader::new_ok(&["01234", "56789"]), "345").unwrap(), true);
    }

    #[test]
    fn test_reads_until_eof() {
        let reader = MockReader::new_ok(&["foo", "bar", ""]);
        assert_eq!(search_file(reader, "baz").unwrap(), false);
    }

    #[test]
    fn test_retries_interrupted() {
        let reader = MockReader::new(vec![Ok("foo"), Err(std::io::Error::new(ErrorKind::Interrupted, "Interrupted")), Ok("bar")]);
        assert_eq!(search_file(reader, "bar").unwrap(), true);
    }

    #[test]
    fn test_propagates_errors() {
        let reader = MockReader::new(vec![Ok("foo"), Err(std::io::Error::new(ErrorKind::BrokenPipe, "Broken"))]);
        assert_eq!(search_file(reader, "b").unwrap_err().kind(), ErrorKind::BrokenPipe);
    }

    #[test]
    fn test_wraparound() {
        let mut data = vec![vec![0; READ_SIZE], vec![1; READ_SIZE], vec![2; READ_SIZE], vec![3; READ_SIZE], vec![4; READ_SIZE]];
        data[3][READ_SIZE - 1] = b'a';
        data[4][0] = b'b';
        let reader = MockReader::new_bytes(data);
        assert_eq!(search_file(reader, "ab").unwrap(), true);
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
            let res = self.results.pop().expect("read called more than expected")?;
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
