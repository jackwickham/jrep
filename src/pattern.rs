#[derive(Debug)]
pub struct Pattern {
    chars: Vec<PatternChar>,
}

impl Pattern {
    pub fn parse(pattern: &str) -> Result<Pattern, String> {
        let mut result = Vec::new();
        let mut input = pattern.bytes();
        Pattern::parse_regular(&mut input, &mut result)?;

        Ok(Pattern{
            chars: result,
        })
    }

    fn parse_regular(input: &mut std::str::Bytes, result: &mut Vec<PatternChar>) -> Result<(), &'static str> {
        while let Some(c) = input.next() {
            match c {
                b'\\' => Pattern::parse_escape(input, result)?,
                b'[' => Pattern::parse_multi(input, result)?,
                b'.' => result.push(PatternChar::Any()),
                _ => result.push(PatternChar::SingleChar(c)),
            }
        }
        Ok(())
    }

    fn parse_escape(input: &mut std::str::Bytes, result: &mut Vec<PatternChar>) -> Result<(), &'static str> {
        match input.next() {
            Some(c) => {
                result.push(PatternChar::SingleChar(c));
                Ok(())
            },
            None => Err("Unexpected end of pattern (expected \\ to start an escape sequence)")
        }
    }

    fn parse_multi(input: &mut std::str::Bytes, result: &mut Vec<PatternChar>) -> Result<(), &'static str> {
        let mut chars = Vec::new();
        let mut negated = false;
        let mut first = true;
        while let Some(c) = input.next() {
            match c {
                b']' if negated => {
                    result.push(PatternChar::Except(chars));
                    return Ok(());
                },
                b']' => {
                    result.push(PatternChar::MultipleChars(chars));
                    return Ok(());
                },
                b'\\' => {
                    match input.next() {
                        Some(c) => chars.push(c),
                        None => return Err("Unexpected end of pattern (expected \\ to start an escape sequence)")
                    }
                },
                b'^' if first => negated = true,
                _ => chars.push(c),
            };
            first = false;
        }

        Err("Unexpected end of pattern (incomplete bracket expression)")
    }

    pub fn len(&self) -> usize {
        self.chars.len()
    }

    pub fn chars(&self) -> &[PatternChar] {
        &self.chars
    }
}

#[derive(Debug)]
pub enum PatternChar {
    SingleChar(u8),
    MultipleChars(Vec<u8>),
    Except(Vec<u8>),
    Any(),
}

impl PatternChar {
    pub fn matches(&self, chr: u8) -> bool {
        match self {
            PatternChar::SingleChar(c) => chr == *c,
            PatternChar::MultipleChars(cs) => cs.contains(&chr),
            PatternChar::Except(cs) => !cs.contains(&chr),
            PatternChar::Any() => true,
        }
    }

    pub fn all_chars(&self) -> Vec<u8> {
        match self {
            PatternChar::SingleChar(c) => vec![*c],
            PatternChar::MultipleChars(cs) => cs.clone(),
            PatternChar::Except(cs) => ((u8::MIN)..=(u8::MAX)).filter(|c| !cs.contains(c)).collect(),
            PatternChar::Any() => ((u8::MIN)..=(u8::MAX)).collect(),
        }
    }
}
