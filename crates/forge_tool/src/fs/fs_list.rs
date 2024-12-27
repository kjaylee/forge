use std::path::Path;

use forge_tool_macros::Description as DescriptionDerive;
use forge_walker::Walker;
use glob::Pattern;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::{Description, ToolTrait};

#[derive(Deserialize, JsonSchema)]
pub struct FSListInput {
    #[schemars(
        description = "The path of the directory to list contents for (relative to the current working directory {{cwd}})"
    )]
    pub path: String,
    #[schemars(
        description = "Whether to list files recursively. Use true for recursive listing, false or omit for top-level only."
    )]
    pub recursive: Option<bool>,
    #[schemars(
        description = "A glob pattern to filter the results. Use patterns like '*.rs' for Rust files, '**/*.txt' for all text files recursively, or 'src/*.js' for JavaScript files in src directory."
    )]
    pub pattern: Option<String>,
}

/// Request to list files and directories within the specified directory. If
/// recursive is true, it will list all files and directories recursively. If
/// recursive is false or not provided, it will only list the top-level
/// contents. Do not use this tool to confirm the existence of files you may
/// have created, as the user will let you know if the files were created
/// successfully or not. Parameters:
/// - path: (required) The path of the directory to list contents for (relative
///   to the current working directory {{cwd}})
/// - recursive: (optional) Whether to list files recursively. Use true for
///   recursive listing, false or omit for top-level only.
/// - pattern: (optional) A glob pattern to filter the results. Use patterns
///   like '*.rs' for Rust files, '**/*.txt' for all text files recursively, or
///   'src/*.js' for JavaScript files in src directory.
#[derive(DescriptionDerive)]
pub struct FSList;

#[async_trait::async_trait]
impl ToolTrait for FSList {
    type Input = FSListInput;
    type Output = Vec<String>;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let dir = Path::new(&input.path);
        if !dir.exists() {
            return Err("Directory does not exist".to_string());
        }

        let pattern = input
            .pattern
            .map(|p| Pattern::new(&p).map_err(|e| e.to_string()))
            .transpose()?;

        let recursive = input.recursive.unwrap_or(false);
        let max_depth = if recursive { usize::MAX } else { 1 };
        let walker = Walker::new(dir.to_path_buf()).with_max_depth(max_depth);

        let files = walker.get().await.map_err(|e| e.to_string())?;

        Ok(files
            .into_iter()
            .filter(|f| f.path != dir.to_string_lossy() && !f.path.is_empty())
            .filter(|f| {
                if let Some(ref pattern) = pattern {
                    return pattern.matches(&f.path);
                }
                true
            })
            .map(|f| {
                let prefix = if f.is_dir { "[DIR]" } else { "[FILE]" };
                format!("{} {}", prefix, f.path)
            })
            .collect())
    }
}

#[cfg(test)]
mod test {
    use tempfile::TempDir;
    use tokio::fs;

    use super::*;

    #[tokio::test]
    async fn test_fs_list_empty_directory() {
        let temp_dir = TempDir::new().unwrap();

        let fs_list = FSList;
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: None,
                pattern: None,
            })
            .await
            .unwrap();

        assert!(result.is_empty());
    }

    #[tokio::test]
    async fn test_fs_list_with_files_and_dirs() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("file1.txt"), "content1")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("file2.txt"), "content2")
            .await
            .unwrap();
        fs::create_dir(temp_dir.path().join("dir1")).await.unwrap();
        fs::create_dir(temp_dir.path().join("dir2")).await.unwrap();

        let fs_list = FSList;
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: None,
                pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 4);

        let files: Vec<_> = result.iter().filter(|p| p.starts_with("[FILE]")).collect();
        let dirs: Vec<_> = result.iter().filter(|p| p.starts_with("[DIR]")).collect();

        assert_eq!(files.len(), 2);
        assert_eq!(dirs.len(), 2);

        assert!(result.iter().any(|p| p.contains("file1.txt")));
        assert!(result.iter().any(|p| p.contains("file2.txt")));
        assert!(result.iter().any(|p| p.contains("dir1")));
        assert!(result.iter().any(|p| p.contains("dir2")));
    }

    #[tokio::test]
    async fn test_fs_list_nonexistent_directory() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_dir = temp_dir.path().join("nonexistent");

        let fs_list = FSList;
        let result = fs_list
            .call(FSListInput {
                path: nonexistent_dir.to_string_lossy().to_string(),
                recursive: None,
                pattern: None,
            })
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_list_with_hidden_files() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("regular.txt"), "content")
            .await
            .unwrap();
        fs::write(temp_dir.path().join(".hidden"), "content")
            .await
            .unwrap();
        fs::create_dir(temp_dir.path().join(".hidden_dir"))
            .await
            .unwrap();

        let fs_list = FSList;
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: None,
                pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 1);
        assert!(result.iter().any(|p| p.contains("regular.txt")));
    }

    #[tokio::test]
    async fn test_fs_list_recursive() {
        let temp_dir = TempDir::new().unwrap();

        // Create nested directory structure
        fs::create_dir(temp_dir.path().join("dir1")).await.unwrap();
        fs::write(temp_dir.path().join("dir1/file1.txt"), "content1")
            .await
            .unwrap();
        fs::create_dir(temp_dir.path().join("dir1/subdir"))
            .await
            .unwrap();
        fs::write(temp_dir.path().join("dir1/subdir/file2.txt"), "content2")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("root.txt"), "content3")
            .await
            .unwrap();

        let fs_list = FSList;

        // Test recursive listing
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(true),
                pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 5); // root.txt, dir1, file1.txt, subdir, file2.txt
        assert!(result.iter().any(|p| p.contains("root.txt")));
        assert!(result.iter().any(|p| p.contains("dir1")));
        assert!(result.iter().any(|p| p.contains("file1.txt")));
        assert!(result.iter().any(|p| p.contains("subdir")));
        assert!(result.iter().any(|p| p.contains("file2.txt")));

        // Test non-recursive listing of same structure
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(false),
                pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 2); // Only root.txt and dir1
        assert!(result.iter().any(|p| p.contains("root.txt")));
        assert!(result.iter().any(|p| p.contains("dir1")));
        assert!(!result.iter().any(|p| p.contains("file1.txt")));
        assert!(!result.iter().any(|p| p.contains("subdir")));
        assert!(!result.iter().any(|p| p.contains("file2.txt")));
    }

    #[tokio::test]
    async fn test_fs_list_with_pattern() {
        let temp_dir = TempDir::new().unwrap();

        // Create test files
        std::fs::write(temp_dir.path().join("test.txt"), "test content").unwrap();
        std::fs::write(temp_dir.path().join("test.rs"), "rust content").unwrap();
        std::fs::write(temp_dir.path().join("TEST.RS"), "uppercase content").unwrap();
        std::fs::create_dir(temp_dir.path().join("src")).unwrap();
        std::fs::write(temp_dir.path().join("src").join("main.rs"), "main content").unwrap();

        // Test exact file pattern
        let result = FSList
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(true),
                pattern: Some("test.txt".to_string()),
            })
            .await
            .unwrap();
        assert_eq!(result.len(), 1);
        assert!(result[0].contains("test.txt"));

        // Test wildcard pattern for Rust files
        let result = FSList
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(true),
                pattern: Some("*.rs".to_string()),
            })
            .await
            .unwrap();
        assert_eq!(result.len(), 2); // Should match test.rs and src/main.rs
        assert!(result.iter().any(|p| p.contains("test.rs")));
        assert!(result.iter().any(|p| p.contains("main.rs")));

        // Test directory-specific pattern
        let result = FSList
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(true),
                pattern: Some("src/*.rs".to_string()),
            })
            .await
            .unwrap();
        assert_eq!(result.len(), 1);
        assert!(result[0].contains("main.rs"));

        // Test non-matching pattern
        let result = FSList
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(true),
                pattern: Some("*.go".to_string()),
            })
            .await
            .unwrap();
        assert_eq!(result.len(), 0);
    }
}
