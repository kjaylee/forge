use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::Deserialize;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;
use tempfile::NamedTempFile;

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

struct Block {
    search: String,
    replace: String,
}

fn parse_blocks(diff: &str) -> Result<Vec<Block>, String> {
    let mut blocks = Vec::new();
    let mut pos = 0;

    while let Some(search_start) = diff[pos..].find("<<<<<<< SEARCH") {
        let search_start = pos + search_start + "<<<<<<< SEARCH".len();
        
        let Some(separator) = diff[search_start..].find("=======") else {
            return Err("Invalid diff format: Missing separator".to_string());
        };
        let separator = search_start + separator;
        
        let Some(replace_end) = diff[separator..].find(">>>>>>> REPLACE") else {
            return Err("Invalid diff format: Missing end marker".to_string());
        };
        let replace_end = separator + replace_end;
        
        blocks.push(Block {
            search: diff[search_start..separator].trim().to_string(),
            replace: diff[separator + "=======".len()..replace_end].trim().to_string(),
        });
        
        pos = replace_end + ">>>>>>> REPLACE".len();
    }

    if blocks.is_empty() {
        return Err("Invalid diff format: No valid blocks found".to_string());
    }

    Ok(blocks)
}

fn apply_changes<P: AsRef<Path>>(path: P, blocks: Vec<Block>) -> Result<(), String> {
    let file = File::open(&path).map_err(|e| e.to_string())?;
    let reader = BufReader::new(file);
    let mut temp_file = NamedTempFile::new().map_err(|e| e.to_string())?;
    let mut current_block = 0;
    let mut buffer = String::new();
    let mut lines = reader.lines();

    // Handle empty search case (new file)
    if blocks[0].search.is_empty() {
        if !blocks[0].replace.is_empty() {
            writeln!(temp_file, "{}", blocks[0].replace)
                .map_err(|e| e.to_string())?;
        }
        temp_file.persist(path).map_err(|e| e.to_string())?;
        return Ok(());
    }

    // Process each line
    while let Some(Ok(line)) = lines.next() {
        if current_block >= blocks.len() {
            writeln!(temp_file, "{}", line).map_err(|e| e.to_string())?;
            continue;
        }

        buffer.push_str(&line);
        buffer.push('\n');

        // Check if we have enough lines to match the search pattern
        let search_lines = blocks[current_block].search.lines().count();
        let buffer_lines: Vec<&str> = buffer.lines().collect();

        if buffer_lines.len() >= search_lines {
            let window = &buffer_lines[buffer_lines.len() - search_lines..];
            let window_text = window.join("\n");

            if window_text.trim() == blocks[current_block].search.trim() {
                // Found a match, write lines before the match
                for line in &buffer_lines[..buffer_lines.len() - search_lines] {
                    writeln!(temp_file, "{}", line).map_err(|e| e.to_string())?;
                }

                // Write replacement and handle line endings
                if !blocks[current_block].replace.is_empty() {
                    write!(temp_file, "{}", blocks[current_block].replace)
                        .map_err(|e| e.to_string())?;
                    if !blocks[current_block].replace.ends_with('\n') {
                        writeln!(temp_file).map_err(|e| e.to_string())?;
                    }
                }

                buffer.clear();
                current_block += 1;
                continue;
            }

            // No match, write the oldest line and remove it from buffer
            let first_line = buffer_lines[0];
            write!(temp_file, "{}", first_line).map_err(|e| e.to_string())?;
            if !first_line.ends_with('\n') {
                writeln!(temp_file).map_err(|e| e.to_string())?;
            }
            buffer = buffer_lines[1..].join("\n");
        }
    }

    // Write any remaining buffered lines
    if !buffer.is_empty() {
        write!(temp_file, "{}", buffer).map_err(|e| e.to_string())?;
    }

    temp_file.persist(path).map_err(|e| e.to_string())?;
    Ok(())
}

#[async_trait::async_trait]
impl ToolTrait for FSReplace {
    type Input = FSReplaceInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let blocks = parse_blocks(&input.diff)?;
        apply_changes(&input.path, blocks)?;
        Ok(format!("Successfully replaced content in {}", input.path))
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;
    use tempfile::TempDir;

    use super::*;

    async fn write_test_file(path: impl AsRef<Path>, content: &str) -> Result<(), String> {
        let mut file = File::create(path).map_err(|e| e.to_string())?;
        file.write_all(content.as_bytes()).map_err(|e| e.to_string())?;
        Ok(())
    }

    async fn read_test_file(path: impl AsRef<Path>) -> Result<String, String> {
        let mut file = File::open(path).map_err(|e| e.to_string())?;
        let mut content = String::new();
        file.read_to_string(&mut content).map_err(|e| e.to_string())?;
        Ok(content)
    }

    #[tokio::test]
    async fn test_line_trimmed_match() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "    Hello World    \n  Test Line  \n   Goodbye World   \n";

        write_test_file(&file_path, content).await.unwrap();

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

        let new_content = read_test_file(&file_path).await.unwrap();
        assert_eq!(
            new_content,
            "Hi World\n  Test Line  \n   Goodbye World   \n"
        );
    }

    #[tokio::test]
    async fn test_empty_search_new_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        write_test_file(&file_path, "").await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\n=======\nNew content\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = read_test_file(&file_path).await.unwrap();
        assert_eq!(new_content, "New content\n");
    }

    #[tokio::test]
    async fn test_multiple_blocks() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        write_test_file(&file_path, content).await.unwrap();

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

        let new_content = read_test_file(&file_path).await.unwrap();
        assert_eq!(new_content, "Hi World\nTest Line\nBye World\n");
    }

    #[tokio::test]
    async fn test_empty_block() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World\nTest Line\nGoodbye World\n";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                diff: "<<<<<<< SEARCH\nTest Line\n=======\n>>>>>>> REPLACE\n".to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully replaced"));

        let new_content = read_test_file(&file_path).await.unwrap();
        assert_eq!(new_content, "Hello World\nGoodbye World\n");
    }
}
