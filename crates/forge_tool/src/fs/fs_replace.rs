use forge_tool_macros::Description as DescriptionDerive;
use nom::bytes::complete::{tag, take_until};
use nom::character::complete::multispace0;
use nom::multi::many0;
use nom::{IResult, Parser};
use schemars::JsonSchema;
use serde::Deserialize;

use crate::{Description, ToolTrait};

#[derive(Deserialize, JsonSchema)]
pub struct FSReplaceInput {
    pub path: String,
    pub diff: String,
}

/// Replace sections of content in an existing file using SEARCH/REPLACE blocks
/// that define exact changes to specific parts of the file. This tool should be
/// used when you need to make targeted changes to specific parts of a file.
/// Parameters:
///     - path: (required) The path of the file to modify (relative to the
///       current working directory {{current_working_dir}})
///     - diff: (required) One or more SEARCH/REPLACE blocks following this
///       format: ``` <<<<<<< SEARCH [exact content to find] ======= [new
///       content to replace with] >>>>>>> REPLACE ``` Critical rules:
///       1. SEARCH content must match the associated file section to find
///          EXACTLY:
///          * Match character-for-character including whitespace, indentation,
///            line endings
///          * Include all comments, docstrings, etc.
///       2. SEARCH/REPLACE blocks will ONLY replace the first match occurrence.
///          * Including multiple unique SEARCH/REPLACE blocks if you need to
///            make multiple changes.
///          * Include *just* enough lines in each SEARCH section to uniquely
///            match each set of lines that need to change.
///       3. Keep SEARCH/REPLACE blocks concise:
///          * Break large SEARCH/REPLACE blocks into a series of smaller blocks
///            that each change a small portion of the file.
///          * Include just the changing lines, and a few surrounding lines if
///            needed for uniqueness.
///          * Do not include long runs of unchanging lines in SEARCH/REPLACE
///            blocks.
///          * Each line must be complete. Never truncate lines mid-way through
///            as this can cause matching failures.
///       4. Special operations:
///          * To move code: Use two SEARCH/REPLACE blocks (one to delete from
///            original + one to insert at new location)
///          * To delete code: Use empty REPLACE section
#[derive(DescriptionDerive)]
pub struct FSReplace;

fn parse_block(input: &str) -> IResult<&str, (&str, &str)> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("<<<<<<< SEARCH")(input)?;
    let (input, _) = tag("\n")(input)?;
    let (input, search) = take_until("=======")(input)?;
    let (input, _) = tag("=======")(input)?;
    let (input, _) = tag("\n")(input)?;
    let (input, replace) = take_until(">>>>>>> REPLACE")(input)?;
    let (input, _) = tag(">>>>>>> REPLACE")(input)?;
    let (input, _) = tag("\n")(input)?;
    Ok((input, (search, replace)))
}

fn parse_diff(input: &str) -> Result<Vec<(&str, &str)>, String> {
    // Validate basic format first
    if !input.contains("<<<<<<< SEARCH")
        || !input.contains("=======")
        || !input.contains(">>>>>>> REPLACE")
    {
        return Err("Invalid diff format: Missing required markers".to_string());
    }

    match many0(parse_block).parse(input) {
        Ok((remaining, blocks)) => {
            if !remaining.trim().is_empty() {
                Err("Invalid diff format: Unparsed content remaining".to_string())
            } else if blocks.is_empty() {
                Err("Invalid diff format: No valid blocks found".to_string())
            } else {
                Ok(blocks)
            }
        }
        Err(_) => Err("Invalid diff format: Failed to parse blocks".to_string()),
    }
}

fn detect_line_ending(content: &str) -> &'static str {
    // If any CRLF is found, use that as the line ending
    if content.contains("\r\n") {
        "\r\n"
    } else {
        "\n"
    }
}

fn normalize_line_endings(content: &str, target_ending: &str) -> String {
    let mut result = String::with_capacity(content.len());
    let mut chars = content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\r' && chars.peek() == Some(&'\n') {
            chars.next(); // consume \n
            result.push_str(target_ending);
        } else if c == '\n' || c == '\r' {
            result.push_str(target_ending);
        } else {
            result.push(c);
        }
    }

    result
}

fn find_match(content: &str, search: &str, last_processed_index: usize) -> Option<(usize, usize)> {
    if search.is_empty() {
        return if content.is_empty() {
            Some((0, 0))
        } else {
            Some((0, content.len()))
        };
    }

    let content_from_index = &content[last_processed_index..];
    let line_ending = detect_line_ending(content_from_index);
    let normalized_search = normalize_line_endings(search, line_ending);
    let normalized_content = normalize_line_endings(content_from_index, line_ending);

    // Try exact match first (with normalized line endings)
    if let Some(idx) = normalized_content.find(&normalized_search) {
        let start = last_processed_index + idx;
        let mut end = start;

        // Calculate end position using original content to preserve line endings
        let mut search_lines = search.lines().count();
        let mut pos = start;
        while search_lines > 0 && pos < content.len() {
            if content[pos..].starts_with("\r\n") {
                pos += 2;
                search_lines -= 1;
            } else if content[pos..].starts_with('\n') {
                pos += 1;
                search_lines -= 1;
            } else {
                pos += 1;
            }
        }
        end = pos;

        return Some((start, end));
    }

    // Try line-by-line comparison with proper line ending handling
    let content_lines: Vec<&str> = content_from_index.lines().collect();
    let search_lines: Vec<&str> = search.lines().collect();

    if search_lines.is_empty() {
        return None;
    }

    // Try line-trimmed match
    'outer: for i in 0..content_lines.len() {
        if i + search_lines.len() > content_lines.len() {
            break;
        }

        for (j, search_line) in search_lines.iter().enumerate() {
            let content_line = content_lines[i + j];
            if content_line.trim() != search_line.trim() {
                continue 'outer;
            }
        }

        // Found a match, calculate exact positions
        let mut start = last_processed_index;
        for k in 0..i {
            start += content_lines[k].len() + detect_line_ending(content).len();
        }

        let mut end = start;
        for k in 0..search_lines.len() {
            let content_line = content_lines[i + k];
            end += content_line.len() + detect_line_ending(content).len();
        }

        if end > start {
            end -= detect_line_ending(content).len();
        }

        return Some((start, end));
    }

    None
}

#[async_trait::async_trait]
impl ToolTrait for FSReplace {
    type Input = FSReplaceInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let content = tokio::fs::read_to_string(&input.path)
            .await
            .map_err(|e| e.to_string())?;

        let blocks = parse_diff(&input.diff)?;
        let mut result = String::new();
        let mut last_processed_index = 0;

        let line_ending = detect_line_ending(&content);

        for (search, replace) in blocks {
            let (start, end) = find_match(&content, search, last_processed_index)
                .ok_or_else(|| format!("Could not find match for search block:\n{}", search))?;

            // Add content between last match and this match
            result.push_str(&content[last_processed_index..start]);

            // Add replacement content with proper line ending handling
            if !replace.is_empty() {
                let replace_lines: Vec<&str> = replace.lines().collect();

                // Add lines with proper line ending preservation
                for (i, line) in replace_lines.iter().enumerate() {
                    if i > 0 {
                        result.push_str(line_ending);
                    }
                    result.push_str(line);
                }

                // Count trailing newlines in original replacement
                let mut trailing_newlines = 0;
                let mut chars = replace.chars().rev().peekable();

                while let Some(c) = chars.next() {
                    if c == '\n' {
                        trailing_newlines += 1;
                        if chars.peek() == Some(&'\r') {
                            chars.next(); // consume \r
                        }
                    } else if c == '\r' {
                        trailing_newlines += 1;
                    } else {
                        break;
                    }
                }

                // Add trailing newlines if present in replacement
                if trailing_newlines > 0 {
                    result.push_str(line_ending);
                }
            }

            last_processed_index = end;
            if last_processed_index < content.len() {
                if content[last_processed_index..].starts_with("\r\n") {
                    last_processed_index += 2;
                } else if content[last_processed_index..].starts_with('\n') {
                    last_processed_index += 1;
                }
            }
        }

        // Add remaining content after last match
        if last_processed_index < content.len() {
            result.push_str(&content[last_processed_index..]);
        }

        tokio::fs::write(&input.path, &result)
            .await
            .map_err(|e| e.to_string())?;

        Ok(format!("Successfully replaced content in {}", input.path))
    }
}

#[cfg(test)]
mod test {
    use tempfile::TempDir;
    use tokio::fs;

    use super::*;

    #[tokio::test]
    async fn test_line_trimmed_match() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "    Hello World    \n  Test Line  \n   Goodbye World   \n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nHello World\n=======\nHi World\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(
            new_content,
            "Hi World\n  Test Line  \n   Goodbye World   \n"
        );
    }

    #[tokio::test]
    async fn test_block_anchor_match() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Start\nMiddle1\nMiddle2\nEnd\nOther\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nStart\nMiddle1\nMiddle2\nEnd\n=======\nNewStart\nNewContent\nNewEnd\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "NewStart\nNewContent\nNewEnd\nOther\n");
    }

    #[tokio::test]
    async fn test_empty_search_new_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // Create empty file
        fs::write(&file_path, "").await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\n=======\nNew content\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "New content\n");
    }

    #[tokio::test]
    async fn test_empty_search_full_replacement() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Old content\nMultiple\nLines";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\n=======\nCompletely new content\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Completely new content\n");
    }

    #[tokio::test]
    async fn test_whitespace_preservation() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "    indented line\n  spaces  between  words  \nno-spaces\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\n  spaces  between  words  \n=======\n    new  spaced  line    \n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(
            new_content,
            "    indented line\n    new  spaced  line    \nno-spaces\n"
        );
    }

    #[tokio::test]
    async fn test_fs_replace_single_block() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nHello World\n=======\nHi World\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Hi World\nTest Line\nGoodbye World\n");

        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nGoodbye World\n=======\nBye World\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Hi World\nTest Line\nBye World\n");
    }

    #[tokio::test]
    async fn test_fs_replace_multiple_blocks() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let diff = "<<<<<<< SEARCH\nHello World\n=======\nHi World\n>>>>>>> REPLACE\n<<<<<<< SEARCH\nGoodbye World\n=======\nBye World\n>>>>>>> REPLACE\n".to_string();

        let result = fs_replace
            .call(FSReplaceInput { path: file_path.to_string_lossy().to_string(), diff })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Hi World\nTest Line\nBye World\n");
    }

    #[tokio::test]
    async fn test_fs_replace_no_match() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nNo Match\n=======\nReplacement\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("Could not find match for search block"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, content);
    }

    #[tokio::test]
    async fn test_newline_preservation() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "line1\nline2\nline3\n"; // Note trailing newline

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test replacing content with trailing newline
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nline2\n=======\nnew line 2\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "line1\nnew line 2\nline3\n");

        // Test replacing content without trailing newline but preserving it
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nline3\n=======\nnew line 3\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "line1\nnew line 2\nnew line 3\n");
    }

    #[tokio::test]
    async fn test_error_messages() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "line1\nline2\nline3";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test non-existent file
        let result = fs_replace
            .call(FSReplaceInput {
                path: "non_existent.txt".to_string(),
                diff: "<<<<<<< SEARCH\nline1\n=======\nnew line\n>>>>>>> REPLACE\n".to_string(),
            })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("No such file"));

        // Test invalid diff format
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "Invalid diff format".to_string(),
            })
            .await;

        assert!(result.is_err());

        // Test no match found
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nnonexistent line\n=======\nnew line\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("Could not find match for search block"));
    }

    #[tokio::test]
    async fn test_match_at_file_end() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "start\nmiddle\nend\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test matching and replacing the last line
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nend\n=======\nnew end\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "start\nmiddle\nnew end\n");

        // Test matching and replacing multiple lines at the end
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nmiddle\nnew end\n=======\nreplaced\nlast lines\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "start\nreplaced\nlast lines\n");
    }

    #[tokio::test]
    async fn test_empty_lines() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "line1\n\nline3\n"; // Note empty line

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test matching content with empty lines
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nline1\n\nline3\n=======\nnew line1\nnew line2\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "new line1\nnew line2\n");
    }

    #[tokio::test]
    async fn test_carriage_returns() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "line1\r\nline2\r\nline3\r\n"; // Windows-style line endings

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test matching content with Windows line endings
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nline2\n=======\nnew line\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "line1\r\nnew line\r\nline3\r\n");
    }

    #[tokio::test]
    async fn test_empty_lines_in_replacement() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "line1\nline2\nline3\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test replacing with content containing empty lines
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nline2\n=======\nnew line\n\nother line\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "line1\nnew line\n\nother line\nline3\n");
    }

    #[tokio::test]
    async fn test_block_anchor_with_empty_lines() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Start\n\nMiddle\n\nEnd\nOther";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test block anchor matching with empty lines
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nStart\n\nMiddle\n\nEnd\n=======\nNewStart\n\nNewMiddle\n\nNewEnd\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "NewStart\n\nNewMiddle\n\nNewEnd\nOther");
    }

    #[tokio::test]
    async fn test_exact_match_with_empty_lines() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "First\n\nSecond\n\nThird";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;

        // Test exact matching with empty lines
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nSecond\n\n=======\nNew Second\n\n>>>>>>> REPLACE\n"
                    .to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "First\n\nNew Second\n\nThird");
    }

    #[tokio::test]
    async fn test_fs_replace_empty_block() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nTest Line\n=======\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Hello World\nGoodbye World");
    }
}
