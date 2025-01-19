use std::path::PathBuf;
use thiserror::Error;

use crate::fs::fs_replace_marker::{DIVIDER, REPLACE, SEARCH};

#[derive(Debug, Error)]
pub enum Error {
    #[error("Error in block {position}: {kind}")]
    Block { position: usize, kind: Kind },
    #[error("File not found at path: {0}")]
    FileNotFound(PathBuf),
    #[error("File operation failed: {0}")]
    FileOperation(#[from] std::io::Error),
    #[error("No search/replace blocks found in diff")]
    NoBlocks,
}

#[derive(Debug, Error)]
pub enum Kind {
    #[error("Missing newline after SEARCH marker")]
    SearchNewline,
    #[error("Missing separator between search and replace content")]
    Separator,
    #[error("Missing newline after separator")]
    SeparatorNewline,
    #[error("Missing REPLACE marker")]
    ReplaceMarker,
}

#[derive(Debug)]
pub struct PatchBlock {
    pub search: String,
    pub replace: String,
}

pub fn normalize_line_endings(text: &str) -> String {
    // Only normalize CRLF to LF while preserving the original line endings
    let mut result = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\r' && chars.peek() == Some(&'\n') {
            chars.next(); // Skip the \n since we'll add it below
            result.push('\n');
        } else {
            result.push(c);
        }
    }
    result
}

pub fn parse_blocks(diff: &str) -> Result<Vec<PatchBlock>, Error> {
    let mut blocks = Vec::new();
    let mut pos = 0;
    let mut block_count = 0;

    // Normalize line endings in the diff string while preserving original newlines
    let diff = normalize_line_endings(diff);

    while let Some(search_start) = diff[pos..].find(SEARCH) {
        block_count += 1;
        let search_start = pos + search_start + SEARCH.len();

        // Include the newline after SEARCH marker in the position
        let search_start = match diff[search_start..].find('\n') {
            Some(nl) => search_start + nl + 1,
            None => return Err(Error::Block { position: block_count, kind: Kind::SearchNewline }),
        };

        let Some(separator) = diff[search_start..].find(DIVIDER) else {
            return Err(Error::Block { position: block_count, kind: Kind::Separator });
        };
        let separator = search_start + separator;

        // Include the newline after separator in the position
        let separator_end = separator + DIVIDER.len();
        let separator_end = match diff[separator_end..].find('\n') {
            Some(nl) => separator_end + nl + 1,
            None => {
                return Err(Error::Block { position: block_count, kind: Kind::SeparatorNewline })
            }
        };

        let Some(replace_end) = diff[separator_end..].find(REPLACE) else {
            return Err(Error::Block { position: block_count, kind: Kind::ReplaceMarker });
        };
        let replace_end = separator_end + replace_end;

        let search = &diff[search_start..separator];
        let replace = &diff[separator_end..replace_end];

        blocks.push(PatchBlock { search: search.to_string(), replace: replace.to_string() });

        pos = replace_end + REPLACE.len();
        // Move past the newline after REPLACE if it exists
        if let Some(nl) = diff[pos..].find('\n') {
            pos += nl + 1;
        }
    }

    if blocks.is_empty() {
        return Err(Error::NoBlocks);
    }

    Ok(blocks)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_blocks_missing_separator() {
        let diff = format!("{SEARCH}\nsearch content\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::Separator }
        ));
    }

    #[test]
    fn test_parse_blocks_missing_newline() {
        let diff = format!("{SEARCH}search content");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::SearchNewline }
        ));
    }

    #[test]
    fn test_parse_blocks_missing_separator_newline() {
        let diff = format!("{SEARCH}\nsearch content\n{DIVIDER}content");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::SeparatorNewline }
        ));
    }

    #[test]
    fn test_parse_blocks_missing_replace_marker() {
        let diff = format!("{SEARCH}\nsearch content\n{DIVIDER}\nreplace content\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::ReplaceMarker }
        ));
    }

    #[test]
    fn test_parse_blocks_no_blocks() {
        // Test both an empty string and random content
        let empty_result = parse_blocks("");
        assert!(matches!(empty_result.unwrap_err(), Error::NoBlocks));

        let random_result = parse_blocks("some random content");
        assert!(matches!(random_result.unwrap_err(), Error::NoBlocks));
    }

    #[test]
    fn test_parse_blocks_multiple_blocks_with_error() {
        let diff = format!(
            "{SEARCH}\nfirst block\n{DIVIDER}\nreplacement\n{REPLACE}\n{SEARCH}\nsecond block\n{DIVIDER}missing_newline"
        );
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 2, kind: Kind::SeparatorNewline }
        ));
    }

    #[test]
    fn test_error_messages() {
        // Test error message formatting for block errors
        let diff = format!("{SEARCH}search content");
        let err = parse_blocks(&diff).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error in block 1: Missing newline after SEARCH marker"
        );

        // Test error message for no blocks
        let err = parse_blocks("").unwrap_err();
        assert_eq!(err.to_string(), "No search/replace blocks found in diff");

        // Test file not found error
        let err = Error::FileNotFound(PathBuf::from("nonexistent.txt"));
        assert_eq!(err.to_string(), "File not found at path: nonexistent.txt");
    }
}