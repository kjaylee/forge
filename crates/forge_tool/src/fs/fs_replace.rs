use forge_tool_macros::Description as DescriptionDerive;
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

fn parse_and_apply(content: &str, diff: &str) -> Result<String, String> {
    let mut result = content.to_string();
    let mut current_pos = 0;

    while let Some(search_start) = diff[current_pos..].find("<<<<<<< SEARCH") {
        let search_start = current_pos + search_start + "<<<<<<< SEARCH".len();
        
        let Some(separator) = diff[search_start..].find("=======") else {
            return Err("Invalid diff format: Missing separator".to_string());
        };
        let separator = search_start + separator;
        
        let Some(replace_end) = diff[separator..].find(">>>>>>> REPLACE") else {
            return Err("Invalid diff format: Missing end marker".to_string());
        };
        let replace_end = separator + replace_end;
        
        // Extract search and replace content, handling newlines around markers
        let search = diff[search_start..separator]
            .trim_start_matches('\n')
            .trim_end_matches('\n');
        let replace = diff[separator + "=======".len()..replace_end]
            .trim_start_matches('\n')
            .trim_end_matches('\n');
        
        // Handle empty search case (new file)
        if search.trim().is_empty() {
            result = if replace.trim().is_empty() {
                String::new()
            } else {
                format!("{}\n", replace.trim())
            };
            current_pos = replace_end + ">>>>>>> REPLACE".len();
            continue;
        }

        // Find and replace content
        let search_lines: Vec<&str> = search.lines().collect();
        let result_lines: Vec<&str> = result.lines().collect();
        let mut found = false;

        'outer: for i in 0..result_lines.len() {
            if i + search_lines.len() > result_lines.len() {
                break;
            }

            for (j, search_line) in search_lines.iter().enumerate() {
                if result_lines[i + j].trim() != search_line.trim() {
                    continue 'outer;
                }
            }

            // Found a match, perform replacement
            let mut new_content = String::new();

            // Add lines before match
            for line in &result_lines[..i] {
                new_content.push_str(line);
                new_content.push('\n');
            }

            // Add replacement
            if !replace.is_empty() {
                new_content.push_str(replace);
                if !replace.ends_with('\n') {
                    new_content.push('\n');
                }
            }

            // Add remaining lines
            if i + search_lines.len() < result_lines.len() {
                for line in &result_lines[i + search_lines.len()..] {
                    new_content.push_str(line);
                    new_content.push('\n');
                }
            }

            result = new_content;
            found = true;
            break;
        }

        if !found {
            return Err(format!("Could not find match for search block:\n{}", search));
        }

        current_pos = replace_end + "\n>>>>>>> REPLACE".len();
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

        let result = parse_and_apply(&content, &input.diff)?;

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
