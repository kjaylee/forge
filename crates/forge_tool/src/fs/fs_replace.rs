use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::Deserialize;
use std::collections::VecDeque;

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
///       current working directory {{cwd}})
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

#[derive(Debug)]
struct Block {
    search: String,
    replace: String,
}

fn parse_blocks(diff: &str) -> Result<Vec<Block>, String> {
    if !diff.contains("<<<<<<< SEARCH") || !diff.contains("=======") || !diff.contains(">>>>>>> REPLACE") {
        return Err("Invalid diff format: Missing required markers".to_string());
    }

    let mut blocks = Vec::new();
    let mut lines = diff.lines().collect::<VecDeque<_>>();

    while !lines.is_empty() {
        let mut line = lines.pop_front().unwrap_or_default();
        
        // Skip empty lines and find start of block
        while !lines.is_empty() && !line.contains("<<<<<<< SEARCH") {
            line = lines.pop_front().unwrap_or_default();
        }
        if lines.is_empty() {
            break;
        }

        // Parse search content
        let mut search = Vec::new();
        line = lines.pop_front().unwrap_or_default();
        while !lines.is_empty() && !line.contains("=======") {
            search.push(line);
            line = lines.pop_front().unwrap_or_default();
        }

        // Parse replace content
        let mut replace = Vec::new();
        line = lines.pop_front().unwrap_or_default();
        while !lines.is_empty() && !line.contains(">>>>>>> REPLACE") {
            replace.push(line);
            line = lines.pop_front().unwrap_or_default();
        }

        blocks.push(Block {
            search: search.join("\n"),
            replace: replace.join("\n"),
        });
    }

    if blocks.is_empty() {
        return Err("Invalid diff format: No valid blocks found".to_string());
    }

    Ok(blocks)
}

fn apply_changes(content: &str, blocks: Vec<Block>) -> Result<String, String> {
    let mut result = content.to_string();

    for Block { search, replace } in blocks {
        // Handle empty search case
        if search.is_empty() {
            result = if replace.is_empty() {
                replace
            } else if replace.ends_with('\n') {
                replace
            } else {
                replace + "\n"
            };
            continue;
        }

        // Split content into lines while preserving line endings
        let mut lines: Vec<String> = Vec::new();
        let mut current_line = String::new();
        let mut chars = result.chars().peekable();
        
        while let Some(c) = chars.next() {
            current_line.push(c);
            if c == '\n' || (c == '\r' && chars.peek() == Some(&'\n')) {
                if c == '\r' {
                    current_line.push(chars.next().unwrap());
                }
                lines.push(current_line);
                current_line = String::new();
            }
        }
        if !current_line.is_empty() {
            lines.push(current_line);
        }

        // Use similar for fuzzy matching
        let mut found = false;
        let search_lines: Vec<&str> = search.lines().collect();
        
        'outer: for i in 0..lines.len() {
            if i + search_lines.len() > lines.len() {
                break;
            }

            // Compare each line with whitespace trimmed
            for (j, search_line) in search_lines.iter().enumerate() {
                let content_line = lines[i + j].trim_end_matches(|c| c == '\n' || c == '\r');
                if content_line.trim() != search_line.trim() {
                    continue 'outer;
                }
            }

            // Found a match, perform replacement
            let mut new_content = String::new();
            
            // Add lines before match
            for line in &lines[..i] {
                new_content.push_str(line);
            }

            // Add replacement with proper line endings
            if !replace.is_empty() {
                let mut replace_lines = replace.lines().peekable();
                while let Some(line) = replace_lines.next() {
                    new_content.push_str(line);
                    if replace_lines.peek().is_some() {
                        // Use the same line ending as the first matched line
                        if lines[i].ends_with("\r\n") {
                            new_content.push_str("\r\n");
                        } else {
                            new_content.push('\n');
                        }
                    }
                }

                // Add final line ending if original had one
                let original_line = &lines[i + search_lines.len() - 1];
                let needs_ending = original_line.ends_with('\n') || original_line.ends_with("\r\n");

                if needs_ending {
                    if original_line.ends_with("\r\n") {
                        new_content.push_str("\r\n");
                    } else {
                        new_content.push('\n');
                    }
                }
            }

            // Add remaining lines
            for line in &lines[i + search_lines.len()..] {
                new_content.push_str(line);
            }

            result = new_content;
            found = true;
            break;
        }

        if !found {
            return Err(format!("Could not find match for search block:\n{}", search));
        }
    }

    Ok(result)
}

#[async_trait::async_trait]
impl ToolTrait for FSReplace {
    type Input = FSReplaceInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let content = tokio::fs::read_to_string(&input.path)
            .await
            .map_err(|e| e.to_string())?;

        let blocks = parse_blocks(&input.diff)?;
        let result = apply_changes(&content, blocks)?;

        tokio::fs::write(&input.path, result)
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
    async fn test_empty_search_new_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

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
    async fn test_multiple_blocks() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        fs::write(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let diff = "<<<<<<< SEARCH\nHello World\n=======\nHi World\n>>>>>>> REPLACE\n<<<<<<< SEARCH\nGoodbye World\n=======\nBye World\n>>>>>>> REPLACE\n".to_string();

        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(new_content, "Hi World\nTest Line\nBye World\n");
    }

    #[tokio::test]
    async fn test_empty_block() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

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
        assert_eq!(new_content, "Hello World\nGoodbye World\n");
    }
}
