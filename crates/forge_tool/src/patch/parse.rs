use std::path::PathBuf;

use nom::bytes::complete::{tag, take_until};
use nom::character::complete::line_ending;
use nom::combinator::{map, verify};
use nom::sequence::{delimited, tuple};
use nom::{Err, IResult};
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
    #[error("No search/replace blocks found in content")]
    NoBlocks,
    #[error("Parse error: {0}")]
    Parse(String),
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
    #[error("Incomplete block")]
    Incomplete,
    #[error("Invalid marker position - must start at beginning of line")]
    InvalidMarkerPosition,
}

#[derive(Debug, PartialEq)]
pub struct PatchBlock {
    pub search: String,
    pub replace: String,
}

/// Verify input starts with a newline or is at start of input
fn ensure_line_start(input: &str) -> bool {
    input.is_empty() || input.starts_with('\n') || input.len() == input.trim_start().len()
}

fn parse_search_marker(input: &str) -> IResult<&str, ()> {
    map(
        delimited(
            verify(take_until(SEARCH), ensure_line_start),
            tag(SEARCH),
            line_ending,
        ),
        |_| (),
    )(input)
}

fn parse_search_content(input: &str) -> IResult<&str, String> {
    map(take_until(DIVIDER), |s: &str| s.to_string())(input)
}

fn parse_divider(input: &str) -> IResult<&str, ()> {
    map(
        delimited(
            verify(take_until(DIVIDER), ensure_line_start),
            tag(DIVIDER),
            line_ending,
        ),
        |_| (),
    )(input)
}

fn parse_replace_content(input: &str) -> IResult<&str, String> {
    map(take_until(REPLACE), |s: &str| s.to_string())(input)
}

fn parse_replace_marker(input: &str) -> IResult<&str, ()> {
    map(
        delimited(
            verify(take_until(REPLACE), ensure_line_start),
            tag(REPLACE),
            line_ending,
        ),
        |_| (),
    )(input)
}

fn parse_patch_block(input: &str) -> IResult<&str, PatchBlock> {
    map(
        tuple((
            parse_search_marker,
            parse_search_content,
            parse_divider,
            parse_replace_content,
            parse_replace_marker,
        )),
        |(_, search, _, replace, _)| PatchBlock { search, replace },
    )(input)
}

/// Parse the input string into a series of patch blocks
pub fn parse_blocks(input: &str) -> Result<Vec<PatchBlock>, Error> {
    if !input.contains(SEARCH) {
        return Err(Error::NoBlocks);
    }

    // Early marker position checks
    if let Some(search_idx) = input.find(SEARCH) {
        if !ensure_line_start(&input[..search_idx]) {
            return Err(Error::Block { position: 1, kind: Kind::InvalidMarkerPosition });
        }
        // Check for newline after SEARCH
        if !input[search_idx..].contains(&format!("{SEARCH}\n")) {
            return Err(Error::Block { position: 1, kind: Kind::SearchNewline });
        }
    }

    let mut blocks = Vec::new();
    let mut remaining = input;
    let mut position = 1;

    while !remaining.trim().is_empty() {
        if !remaining.contains(SEARCH) {
            break;
        }

        // Check marker positions before attempting to parse
        if let Some(divider_idx) = remaining.find(DIVIDER) {
            if !ensure_line_start(&remaining[..divider_idx]) {
                return Err(Error::Block { position, kind: Kind::InvalidMarkerPosition });
            }
            // Check for newline after DIVIDER
            if !remaining[divider_idx..].contains(&format!("{DIVIDER}\n")) {
                return Err(Error::Block { position, kind: Kind::SeparatorNewline });
            }
        }
        if let Some(replace_idx) = remaining.find(REPLACE) {
            if !ensure_line_start(&remaining[..replace_idx]) {
                return Err(Error::Block { position, kind: Kind::InvalidMarkerPosition });
            }
            // Check for newline after REPLACE
            if !remaining[replace_idx..].contains(&format!("{REPLACE}\n")) {
                return Err(Error::Block { position, kind: Kind::Incomplete });
            }
        }

        match parse_patch_block(remaining) {
            Ok((rest, block)) => {
                blocks.push(block);
                remaining = rest;
                position += 1;
            }
            Err(Err::Error(_)) => {
                // If we get here, the basic format checks passed but the content is invalid
                if remaining.contains(SEARCH) && !remaining.contains(DIVIDER) {
                    return Err(Error::Block { position, kind: Kind::Separator });
                } else if remaining.contains(DIVIDER) && !remaining.contains(REPLACE) {
                    return Err(Error::Block { position, kind: Kind::ReplaceMarker });
                }
                return Err(Error::Parse("Invalid patch format".to_string()));
            }
            Err(Err::Incomplete(_)) => {
                return Err(Error::Block { position, kind: Kind::Incomplete });
            }
            Err(e) => {
                return Err(Error::Parse(e.to_string()));
            }
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
        assert_eq!(err.to_string(), "No search/replace blocks found in content");

        // Test file not found error
        let err = Error::FileNotFound(PathBuf::from("nonexistent.txt"));
        assert_eq!(err.to_string(), "File not found at path: nonexistent.txt");
    }

    #[test]
    fn test_valid_single_block() {
        let diff = format!("{SEARCH}\nold code\n{DIVIDER}\nnew code\n{REPLACE}\n");
        let result = parse_blocks(&diff).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].search, "old code\n");
        assert_eq!(result[0].replace, "new code\n");
    }

    #[test]
    fn test_valid_multiple_blocks() {
        let diff = format!(
            "{SEARCH}\nfirst old\n{DIVIDER}\nfirst new\n{REPLACE}\n{SEARCH}\nsecond old\n{DIVIDER}\nsecond new\n{REPLACE}\n"
        );
        let result = parse_blocks(&diff).unwrap();
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].search, "first old\n");
        assert_eq!(result[0].replace, "first new\n");
        assert_eq!(result[1].search, "second old\n");
        assert_eq!(result[1].replace, "second new\n");
    }

    #[test]
    fn test_empty_sections() {
        let diff = format!("{SEARCH}\n{DIVIDER}\n{REPLACE}\n");
        let result = parse_blocks(&diff).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].search, "");
        assert_eq!(result[0].replace, "");
    }

    #[test]
    fn test_whitespace_preservation() {
        let diff = format!(
            "{SEARCH}\n    indented\n\n  spaces  \n{DIVIDER}\n\tindented\n\n\ttabbed\n{REPLACE}\n"
        );
        let result = parse_blocks(&diff).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].search, "    indented\n\n  spaces  \n");
        assert_eq!(result[0].replace, "\tindented\n\n\ttabbed\n");
    }

    #[test]
    fn test_unicode_content() {
        let diff = format!("{SEARCH}\n🦀 Rust\n{DIVIDER}\n📦 Crate\n{REPLACE}\n");
        let result = parse_blocks(&diff).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].search, "🦀 Rust\n");
        assert_eq!(result[0].replace, "📦 Crate\n");
    }

    #[test]
    fn test_marker_must_start_at_line_beginning() {
        // Test SEARCH marker
        let diff = format!("  {SEARCH}\ncode\n{DIVIDER}\nnew\n{REPLACE}\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::InvalidMarkerPosition }
        ));

        // Test DIVIDER marker
        let diff = format!("{SEARCH}\ncode\n  {DIVIDER}\nnew\n{REPLACE}\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::InvalidMarkerPosition }
        ));

        // Test REPLACE marker
        let diff = format!("{SEARCH}\ncode\n{DIVIDER}\nnew\n  {REPLACE}\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::InvalidMarkerPosition }
        ));
    }

    #[test]
    fn test_markers_must_end_with_newline() {
        // Test SEARCH marker
        let diff = format!("{SEARCH}code\n{DIVIDER}\nnew\n{REPLACE}\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::SearchNewline }
        ));

        // Test DIVIDER marker
        let diff = format!("{SEARCH}\ncode\n{DIVIDER}new\n{REPLACE}\n");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::SeparatorNewline }
        ));

        // Test REPLACE marker without newline
        let diff = format!("{SEARCH}\ncode\n{DIVIDER}\nnew\n{REPLACE}");
        let result = parse_blocks(&diff);
        assert!(matches!(
            result.unwrap_err(),
            Error::Block { position: 1, kind: Kind::Incomplete }
        ));
    }
}
