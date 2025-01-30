use std::fmt;
use std::path::Path;

use nom::branch::alt;
use nom::bytes::complete::take_while1;
use nom::character::complete::{char, space0, space1};
use nom::combinator::{map, opt, recognize};
use nom::multi::many0;
use nom::sequence::{pair, preceded};
use nom::{IResult, Parser};

#[derive(Debug, Clone)]
pub struct Prompt {
    tokens: Vec<Token>,
}

impl fmt::Display for Prompt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for token in &self.tokens {
            if !first {
                write!(f, " ")?; // Write the separator directly
            } else {
                first = false;
            }
            match token {
                Token::Literal(s) => write!(f, "{}", s)?,
                Token::File(s) => write!(f, "@{}", s)?,
            }
        }
        Ok(())
    }
}

impl Prompt {
    pub fn new(content: impl Into<String>) -> Prompt {
        Prompt { tokens: vec![Token::Literal(content.into())] }
    }
    pub fn files(&self) -> Vec<String> {
        let mut seen = std::collections::HashSet::new();
        self.tokens
            .iter()
            .filter_map(|t| match t {
                Token::File(s) => {
                    if seen.insert(s.clone()) {
                        Some(s.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Literal(String),
    File(String),
}

impl Prompt {
    // TODO: make `parse` pub(crate)
    pub fn parse(message: String) -> Prompt {
        let tokens = match Self::parse_tokens(&message) {
            Ok((_, tokens)) => tokens,
            Err(_) => vec![Token::Literal(message)], // Fallback for unparsable input
        };

        Prompt { tokens }
    }

    fn parse_tokens(input: &str) -> IResult<&str, Vec<Token>> {
        many0(alt((
            Self::parse_file_path,
            map(Self::parse_word, Token::Literal),
        )))
        .parse(input)
    }

    /// considers only valid file paths.
    fn parse_file_path(input: &str) -> IResult<&str, Token> {
        map(
            preceded(
                char('@'),
                take_while1(|c: char| !c.is_whitespace() && c != '@'),
            ),
            |path: &str| {
                if Path::new(path).exists() {
                    Token::File(path.to_string())
                } else {
                    Token::Literal(format!("@{}", path))
                }
            },
        )
        .parse(input)
    }

    fn parse_word(input: &str) -> IResult<&str, String> {
        let (input, _) = space0(input)?;
        let (input, word) = recognize(pair(
            take_while1(|c: char| !c.is_whitespace()),
            opt(space1),
        ))
        .parse(input)?;
        Ok((input, word.trim().to_string()))
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use std::fs;
    use tempfile::TempDir;

    use super::*;

    struct Fixture {
        _temp_dir: TempDir,
    }

    impl Default for Fixture {
        fn default() -> Self {
            let temp_dir = tempfile::tempdir().unwrap();
            fs::create_dir_all(temp_dir.path().join("src")).unwrap();
            fs::write(temp_dir.path().join("src/test_file.txt"), "test content").unwrap();
            fs::write(temp_dir.path().join("src/test_file2.txt"), "test content").unwrap();
            fs::write(temp_dir.path().join("src/a.txt"), "test content").unwrap();
            fs::write(temp_dir.path().join("src/b.txt"), "test content").unwrap();
            fs::write(temp_dir.path().join("src/测试文件.txt"), "test content").unwrap();
            Self { _temp_dir: temp_dir }
        }
    }

    impl Fixture {
        fn path(&self, ext: &str) -> String {
            self._temp_dir.path().join(ext).display().to_string()
        }
    }

    #[test]
    fn test_with_existing_file() {
        let fixture = Fixture::default();
        let file_path = fixture.path("src/test_file.txt");
        let prompt = Prompt::parse(format!(
            "Please check this file: @{} for content",
            file_path
        ));
        assert_eq!(prompt.files(), vec![file_path]);
    }

    #[test]
    fn test_with_file_reference_at_end() {
        let fixture = Fixture::default();
        let file_path = fixture.path("src/test_file.txt");
        let prompt = Prompt::parse(format!("Check this file @{}", file_path));
        assert_eq!(prompt.files(), vec![file_path]);
    }

    #[test]
    fn test_with_unicode_characters() {
        let fixture = Fixture::default();
        let file_path = fixture.path("src/测试文件.txt");
        let prompt = Prompt::parse(format!("Check this Unicode path: @{}", file_path));
        assert_eq!(prompt.files(), vec![file_path]);
    }

    #[test]
    fn test_with_consecutive_file_references() {
        let fixture = Fixture::default();
        let file_a = fixture.path("src/a.txt");
        let file_b = fixture.path("src/b.txt");
        let prompt = Prompt::parse(format!("@{}@{}", file_a, file_b));
        assert_eq!(prompt.files(), vec![file_a, file_b]);
    }

    #[test]
    fn test_with_duplicate_file_references() {
        let fixture = Fixture::default();
        let file_path = fixture.path("src/test_file.txt");
        let prompt = Prompt::parse(format!("Check this file: @{} @{}", file_path, file_path));
        assert_eq!(prompt.files(), vec![file_path]);
    }

    #[test]
    fn test_with_file_reference_at_start() {
        let fixture = Fixture::default();
        let file_path = fixture.path("src/test_file.txt");
        let prompt = Prompt::parse(format!("@{} contains some content", file_path));
        assert_eq!(prompt.files(), vec![file_path]);
    }

    #[test]
    fn test_with_multiple_files() {
        let fixture = Fixture::default();
        let file1 = fixture.path("src/test_file.txt");
        let file2 = fixture.path("src/test_file2.txt");
        let prompt = Prompt::parse(format!("Compare @{} with @{}", file1, file2));
        assert_eq!(prompt.files(), vec![file1, file2]);
    }

    #[test]
    fn test_with_no_files() {
        let prompt = Prompt::parse("Just a regular message".to_string());
        assert_eq!(prompt.files(), Vec::<String>::new());
        assert_eq!(prompt.to_string(), "Just a regular message");
    }

    #[test]
    fn test_with_empty_input() {
        let prompt = Prompt::parse("".to_string());
        assert_eq!(prompt.files(), Vec::<String>::new());
        assert_eq!(prompt.to_string(), "");
    }

    #[test]
    fn test_file_markers() {
        let prompt = Prompt::parse("hey there, this is my test@mail.com id.".to_string());
        assert!(prompt.files().is_empty());
        assert_eq!(prompt.to_string(), "hey there, this is my test@mail.com id.");
    }

    #[test]
    fn test_if_file_not_exist_treat_it_literal() {
        let prompt = Prompt::parse("hey there, this is my @/ext/test.md id.".to_string());
        assert!(prompt.files().is_empty());
        assert_eq!(prompt.to_string(), "hey there, this is my @/ext/test.md id.");
    }

    #[test]
    fn test_consecutive_file_refs() {
        let fixture = Fixture::default();
        let file1 = fixture.path("src/test_file.txt");
        let file2 = fixture.path("src/test_file2.txt");
        let prompt = Prompt::parse(format!("@{}@{}", file1, file2));
        assert_eq!(prompt.files(), vec![file1, file2]);
    }
}
