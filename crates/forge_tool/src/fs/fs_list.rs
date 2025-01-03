use std::path::Path;

use forge_tool_macros::Description as DescriptionDerive;
use forge_walker::Walker;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{Description, ToolCallService};

#[derive(Deserialize, JsonSchema)]
pub struct FSListInput {
    /// The path of the directory to list contents for (relative to the current
    /// working directory)
    pub path: String,
    /// Whether to list files recursively. Use true for recursive listing, false
    /// or omit for top-level only.
    pub recursive: Option<bool>,
}

/// Request to list files and directories within the specified directory. If
/// recursive is true, it will list all files and directories recursively. If
/// recursive is false or not provided, it will only list the top-level
/// contents. Do not use this tool to confirm the existence of files you may
/// have created, as the user will let you know if the files were created
/// successfully or not.
#[derive(DescriptionDerive)]
pub struct FSList;

#[derive(Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename = "fs_list")]
pub struct FSListOutput {
    #[serde(rename = "@path")]
    path: String,
    #[serde(rename = "@recursive")]
    #[serde(skip_serializing_if = "Option::is_none")]
    recursive: Option<bool>,
    #[serde(rename = "$value")]
    entries: Vec<FileType>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum FileType {
    Dir(String),
    File(String),
}

#[async_trait::async_trait]
impl ToolCallService for FSList {
    type Input = FSListInput;
    type Output = FSListOutput;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let dir = Path::new(&input.path);
        if !dir.exists() {
            return Err("Directory does not exist".to_string());
        }

        let mut paths = Vec::new();
        let recursive = input.recursive.unwrap_or(false);
        let max_depth = if recursive { usize::MAX } else { 1 };
        let walker = Walker::new(dir.to_path_buf()).with_max_depth(max_depth);

        let files = walker.get().await.map_err(|e| e.to_string())?;

        for entry in files {
            // Skip the root directory itself
            if entry.path == dir.to_string_lossy() {
                continue;
            }

            if !entry.path.is_empty() {
                let entry_type = if entry.is_dir {
                    FileType::Dir(entry.path)
                } else {
                    FileType::File(entry.path)
                };
                paths.push(entry_type);
            }
        }

        Ok(FSListOutput { path: input.path, recursive: input.recursive, entries: paths })
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
            })
            .await
            .unwrap();

        assert!(result.entries.is_empty());
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
            })
            .await
            .unwrap();

        assert_eq!(result.entries.len(), 4);

        let files: Vec<_> = result
            .entries
            .iter()
            .filter(|p| {
                if let FileType::File(_) = p {
                    true
                } else {
                    false
                }
            })
            .collect();
        let dirs: Vec<_> = result
            .entries
            .iter()
            .filter(|p| {
                if let FileType::Dir(_) = p {
                    true
                } else {
                    false
                }
            })
            .collect();

        assert_eq!(files.len(), 2);
        assert_eq!(dirs.len(), 2);
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
            })
            .await
            .unwrap();

        assert_eq!(result.entries.len(), 1);
        assert!(result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("regular.txt")
            } else {
                false
            }
        }));
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
            })
            .await
            .unwrap();

        assert_eq!(result.entries.len(), 5); // root.txt, dir1, file1.txt, subdir, file2.txt
        assert!(result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("root.txt")
            } else {
                false
            }
        }));
        assert!(result.entries.iter().any(|p| {
            if let FileType::Dir(dir_name) = p {
                dir_name.contains("dir1")
            } else {
                false
            }
        }));
        assert!(result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("file1.txt")
            } else {
                false
            }
        }));
        assert!(result.entries.iter().any(|p| {
            if let FileType::Dir(dir_name) = p {
                dir_name.contains("subdir")
            } else {
                false
            }
        }));
        assert!(result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("file2.txt")
            } else {
                false
            }
        }));

        // Test non-recursive listing of same structure
        let result = fs_list
            .call(FSListInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                recursive: Some(false),
            })
            .await
            .unwrap();

        assert_eq!(result.entries.len(), 2); // Only root.txt and dir1
        assert!(result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("root.txt")
            } else {
                false
            }
        }));
        assert!(result.entries.iter().any(|p| {
            if let FileType::Dir(dir_name) = p {
                dir_name.contains("dir1")
            } else {
                false
            }
        }));
        assert!(!result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("file1.txt")
            } else {
                false
            }
        }));
        assert!(!result.entries.iter().any(|p| {
            if let FileType::Dir(dir_name) = p {
                dir_name.contains("subdir")
            } else {
                false
            }
        }));
        assert!(!result.entries.iter().any(|p| {
            if let FileType::File(file_name) = p {
                file_name.contains("file2.txt")
            } else {
                false
            }
        }));
    }

    #[test]
    fn serialize_to_xml() {
        let output = FSListOutput {
            path: ".".to_string(),
            recursive: None,
            entries: vec![
                FileType::Dir("dir1".to_string()),
                FileType::File("file1.txt".to_string()),
            ],
        };

        let mut buffer = Vec::new();
        let mut writer = quick_xml::Writer::new_with_indent(&mut buffer, b' ', 4);
        writer
            .write_serializable("fs_list", &output)
            .unwrap();

        let xml_str = std::str::from_utf8(&buffer).unwrap();
        insta::assert_snapshot!(xml_str);
    }
}
