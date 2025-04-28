use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use base64::Engine;
use forge_domain::{Attachment, AttachmentService, ContentType, EnvironmentService};

use crate::{FsReadService, Infrastructure};
// TODO: bring pdf support, pdf is just a collection of images.

#[derive(Clone)]
pub struct ForgeChatRequest<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> ForgeChatRequest<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    async fn prepare_attachments<T: AsRef<Path>>(
        &self,
        paths: HashSet<T>,
    ) -> anyhow::Result<Vec<Attachment>> {
        futures::future::join_all(
            paths
                .into_iter()
                .map(|v| v.as_ref().to_path_buf())
                .map(|v| self.populate_attachments(v)),
        )
        .await
        .into_iter()
        .collect::<anyhow::Result<Vec<_>>>()
    }

    async fn populate_attachments(&self, mut path: PathBuf) -> anyhow::Result<Attachment> {
        let extension = path.extension().map(|v| v.to_string_lossy().to_string());
        if !path.is_absolute() {
            path = self
                .infra
                .environment_service()
                .get_environment()
                .cwd
                .join(path)
        }
        let file_content = self.infra.file_read_service().read(path.as_path()).await?;
        let path = path.to_string_lossy().to_string();
        if let Some(img_extension) = extension.and_then(|ext| match ext.as_str() {
            "jpeg" | "jpg" => Some("jpeg"),
            "png" => Some("png"),
            "webp" => Some("webp"),
            _ => None,
        }) {
            // For image files, we need to convert the string back to bytes for base64
            // encoding
            let bytes = file_content.as_bytes();
            let base_64_encoded = base64::engine::general_purpose::STANDARD.encode(bytes);
            let content = format!("data:image/{img_extension};base64,{base_64_encoded}");
            Ok(Attachment { content, path, content_type: ContentType::Image })
        } else {
            // For text files, we can use the content directly
            Ok(Attachment { content: file_content, path, content_type: ContentType::Text })
        }
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> AttachmentService for ForgeChatRequest<F> {
    async fn attachments(&self, url: &str) -> anyhow::Result<Vec<Attachment>> {
        self.prepare_attachments(Attachment::parse_all(url)).await
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Mutex};

    use base64::Engine;
    use bytes::Bytes;
    use forge_domain::{
        AttachmentService, CommandOutput, ContentType, Environment, EnvironmentService, Provider,
    };
    use forge_snaps::Snapshot;

    use crate::attachment::ForgeChatRequest;
    use crate::{
        CommandExecutorService, FileRemoveService, FsCreateDirsService, FsMetaService,
        FsReadService, FsSnapshotService, FsWriteService, Infrastructure,
    };

    #[derive(Debug)]
    pub struct MockEnvironmentService {}

    #[async_trait::async_trait]
    impl EnvironmentService for MockEnvironmentService {
        fn get_environment(&self) -> Environment {
            Environment {
                os: "test".to_string(),
                pid: 12345,
                cwd: PathBuf::from("/test"),
                home: Some(PathBuf::from("/home/test")),
                shell: "bash".to_string(),
                base_path: PathBuf::from("/base"),
                provider: Provider::open_router("test-key"),
                retry_config: Default::default(),
            }
        }
    }

    impl MockFileService {
        fn new() -> Self {
            let mut files = HashMap::new();
            // Add some mock files
            files.insert(
                PathBuf::from("/test/file1.txt"),
                "This is a text file content".to_string(),
            );
            files.insert(
                PathBuf::from("/test/image.png"),
                "mock-binary-content".to_string(),
            );
            files.insert(
                PathBuf::from("/test/image with spaces.jpg"),
                "mock-jpeg-content".to_string(),
            );

            Self {
                files: Mutex::new(
                    files
                        .into_iter()
                        .map(|(a, b)| (a, Bytes::from(b)))
                        .collect::<Vec<_>>(),
                ),
            }
        }

        fn add_file(&self, path: PathBuf, content: String) {
            let mut files = self.files.lock().unwrap();
            files.push((path, Bytes::from_owner(content)));
        }
    }

    #[async_trait::async_trait]
    impl FsReadService for MockFileService {
        async fn read(&self, path: &Path) -> anyhow::Result<String> {
            let files = self.files.lock().unwrap();
            match files.iter().find(|v| v.0 == path) {
                Some((_, content)) => {
                    let bytes = content.clone();
                    String::from_utf8(bytes.to_vec())
                        .map_err(|e| anyhow::anyhow!("Invalid UTF-8 in file: {:?}: {}", path, e))
                }
                None => Err(anyhow::anyhow!("File not found: {:?}", path)),
            }
        }
        
        async fn range_read(
            &self,
            path: &Path,
            start_byte: Option<u64>,
            end_byte: Option<u64>,
        ) -> anyhow::Result<(String, forge_fs::FileInfo)> {
            let content = self.read(path).await?;
            let total_size = content.len() as u64;
            
            // Default to reading the whole file if no range is specified
            let start = start_byte.unwrap_or(0);
            if start > total_size {
                return Err(anyhow::anyhow!("Start position exceeds file size"));
            }
            
            let end = end_byte.unwrap_or(total_size).min(total_size);
            if start > end {
                return Err(anyhow::anyhow!("Invalid range: start > end"));
            }
            
            // Extract the requested range
            let range_content = if start < total_size {
                // Using chars() to respect UTF-8 boundaries
                content.chars().skip(start as usize).take((end - start) as usize).collect()
            } else {
                String::new()
            };
            
            Ok((range_content, forge_fs::FileInfo::new(start, end, total_size)))
        }
    }

    #[derive(Debug, Clone)]
    pub struct MockInfrastructure {
        env_service: Arc<MockEnvironmentService>,
        file_service: Arc<MockFileService>,
        file_snapshot_service: Arc<MockSnapService>,
    }

    impl MockInfrastructure {
        pub fn new() -> Self {
            Self {
                env_service: Arc::new(MockEnvironmentService {}),
                file_service: Arc::new(MockFileService::new()),
                file_snapshot_service: Arc::new(MockSnapService),
            }
        }
    }

    #[derive(Debug)]
    pub struct MockFileService {
        files: Mutex<Vec<(PathBuf, Bytes)>>,
    }

    #[async_trait::async_trait]
    impl FileRemoveService for MockFileService {
        async fn remove(&self, path: &Path) -> anyhow::Result<()> {
            if !self.exists(path).await? {
                return Err(anyhow::anyhow!("File not found: {:?}", path));
            }
            self.files.lock().unwrap().retain(|(p, _)| p != path);
            Ok(())
        }
    }

    #[async_trait::async_trait]
    impl FsCreateDirsService for MockFileService {
        async fn create_dirs(&self, path: &Path) -> anyhow::Result<()> {
            self.files
                .lock()
                .unwrap()
                .push((path.to_path_buf(), Bytes::new()));
            Ok(())
        }
    }

    #[async_trait::async_trait]
    impl FsWriteService for MockFileService {
        async fn write(&self, path: &Path, contents: Bytes) -> anyhow::Result<()> {
            let index = self.files.lock().unwrap().iter().position(|v| v.0 == path);
            if let Some(index) = index {
                self.files.lock().unwrap().remove(index);
            }
            self.files
                .lock()
                .unwrap()
                .push((path.to_path_buf(), contents));
            Ok(())
        }
    }

    #[derive(Debug)]
    pub struct MockSnapService;

    #[async_trait::async_trait]
    impl FsSnapshotService for MockSnapService {
        async fn create_snapshot(&self, _: &Path) -> anyhow::Result<Snapshot> {
            unimplemented!()
        }

        async fn undo_snapshot(&self, _: &Path) -> anyhow::Result<()> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl FsMetaService for MockFileService {
        async fn is_file(&self, path: &Path) -> anyhow::Result<bool> {
            Ok(self
                .files
                .lock()
                .unwrap()
                .iter()
                .filter(|v| v.0.extension().is_some())
                .any(|(p, _)| p == path))
        }

        async fn exists(&self, path: &Path) -> anyhow::Result<bool> {
            Ok(self.files.lock().unwrap().iter().any(|(p, _)| p == path))
        }
    }

    #[async_trait::async_trait]
    impl CommandExecutorService for () {
        async fn execute_command(
            &self,
            command: String,
            working_dir: PathBuf,
        ) -> anyhow::Result<CommandOutput> {
            // For test purposes, we'll create outputs that match what the shell tests
            // expect Check for common command patterns
            if command == "echo 'Hello, World!'" {
                // When the test_shell_echo looks for this specific command
                // It's expecting to see "Mock command executed successfully"
                return Ok(CommandOutput {
                    stdout: "Mock command executed successfully\n".to_string(),
                    stderr: "".to_string(),
                    success: true,
                });
            } else if command.contains("echo") {
                if command.contains(">") && command.contains(">&2") {
                    // Commands with both stdout and stderr
                    let stdout = if command.contains("to stdout") {
                        "to stdout\n"
                    } else {
                        "stdout output\n"
                    };
                    let stderr = if command.contains("to stderr") {
                        "to stderr\n"
                    } else {
                        "stderr output\n"
                    };
                    return Ok(CommandOutput {
                        stdout: stdout.to_string(),
                        stderr: stderr.to_string(),
                        success: true,
                    });
                } else if command.contains(">&2") {
                    // Command with only stderr
                    let content = command.split("echo").nth(1).unwrap_or("").trim();
                    let content = content.trim_matches(|c| c == '\'' || c == '"');
                    return Ok(CommandOutput {
                        stdout: "".to_string(),
                        stderr: format!("{content}\n"),
                        success: true,
                    });
                } else {
                    // Standard echo command
                    let content = if command == "echo ''" {
                        "\n".to_string()
                    } else if command.contains("&&") {
                        // Multiple commands
                        "first\nsecond\n".to_string()
                    } else if command.contains("$PATH") {
                        // PATH command returns a mock path
                        "/usr/bin:/bin:/usr/sbin:/sbin\n".to_string()
                    } else {
                        let parts: Vec<&str> = command.split("echo").collect();
                        if parts.len() > 1 {
                            let content = parts[1].trim();
                            // Remove quotes if present
                            let content = content.trim_matches(|c| c == '\'' || c == '"');
                            format!("{content}\n")
                        } else {
                            "Hello, World!\n".to_string()
                        }
                    };

                    return Ok(CommandOutput {
                        stdout: content,
                        stderr: "".to_string(),
                        success: true,
                    });
                }
            } else if command == "pwd" || command == "cd" {
                // Return working directory for pwd/cd commands
                return Ok(CommandOutput {
                    stdout: format!("{working_dir}\n", working_dir = working_dir.display()),
                    stderr: "".to_string(),
                    success: true,
                });
            } else if command == "true" {
                // true command returns success with no output
                return Ok(CommandOutput {
                    stdout: "".to_string(),
                    stderr: "".to_string(),
                    success: true,
                });
            } else if command.starts_with("/bin/ls") || command.contains("whoami") {
                // Full path commands
                return Ok(CommandOutput {
                    stdout: "user\n".to_string(),
                    stderr: "".to_string(),
                    success: true,
                });
            } else if command == "non_existent_command" {
                // Command not found
                return Ok(CommandOutput {
                    stdout: "".to_string(),
                    stderr: "command not found: non_existent_command\n".to_string(),
                    success: false,
                });
            }

            // Default response for other commands
            Ok(CommandOutput {
                stdout: "Mock command executed successfully\n".to_string(),
                stderr: "".to_string(),
                success: true,
            })
        }
    }

    impl Infrastructure for MockInfrastructure {
        type EnvironmentService = MockEnvironmentService;
        type FsReadService = MockFileService;
        type FsWriteService = MockFileService;
        type FsRemoveService = MockFileService;
        type FsMetaService = MockFileService;
        type FsCreateDirsService = MockFileService;
        type FsSnapshotService = MockSnapService;
        type CommandExecutorService = ();

        fn environment_service(&self) -> &Self::EnvironmentService {
            &self.env_service
        }

        fn file_read_service(&self) -> &Self::FsReadService {
            &self.file_service
        }

        fn file_write_service(&self) -> &Self::FsWriteService {
            &self.file_service
        }

        fn file_meta_service(&self) -> &Self::FsMetaService {
            &self.file_service
        }

        fn file_snapshot_service(&self) -> &Self::FsSnapshotService {
            &self.file_snapshot_service
        }

        fn file_remove_service(&self) -> &Self::FsRemoveService {
            &self.file_service
        }

        fn create_dirs_service(&self) -> &Self::FsCreateDirsService {
            &self.file_service
        }

        fn command_executor_service(&self) -> &Self::CommandExecutorService {
            &()
        }
    }

    #[tokio::test]
    async fn test_add_url_with_text_file() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());
        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with a text file path in chat message
        let url = "@[/test/file1.txt]".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert
        // Text files should be included in the attachments
        assert_eq!(attachments.len(), 1);
        let attachment = attachments.first().unwrap();
        assert_eq!(attachment.path, "/test/file1.txt");
        assert_eq!(attachment.content_type, ContentType::Text);
        assert_eq!(attachment.content, "This is a text file content");
    }

    #[tokio::test]
    async fn test_add_url_with_image() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());
        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with an image file
        let url = "@[/test/image.png]".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert
        assert_eq!(attachments.len(), 1);
        let attachment = attachments.first().unwrap();
        assert_eq!(attachment.path, "/test/image.png");
        assert!(matches!(attachment.content_type, ContentType::Image));

        // Base64 content should be the encoded mock binary content with proper data URI
        // format
        let expected_base64 =
            base64::engine::general_purpose::STANDARD.encode("mock-binary-content");
        assert_eq!(
            attachment.content,
            format!("data:image/png;base64,{expected_base64}")
        );
    }

    #[tokio::test]
    async fn test_add_url_with_jpg_image_with_spaces() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());
        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with an image file that has spaces in the path
        let url = "@[/test/image with spaces.jpg]".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert
        assert_eq!(attachments.len(), 1);
        let attachment = attachments.first().unwrap();
        assert_eq!(attachment.path, "/test/image with spaces.jpg");

        // Base64 content should be the encoded mock jpeg content with proper data URI
        // format
        let expected_base64 = base64::engine::general_purpose::STANDARD.encode("mock-jpeg-content");
        assert_eq!(
            attachment.content,
            format!("data:image/jpeg;base64,{expected_base64}")
        );
    }

    #[tokio::test]
    async fn test_add_url_with_multiple_files() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());

        // Add an extra file to our mock service
        infra.file_service.add_file(
            PathBuf::from("/test/file2.txt"),
            "This is another text file".to_string(),
        );

        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with multiple files mentioned
        let url = "@[/test/file1.txt] @[/test/file2.txt] @[/test/image.png]".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert
        // All files should be included in the attachments
        assert_eq!(attachments.len(), 3);

        // Verify that each expected file is in the attachments
        let has_file1 = attachments
            .iter()
            .any(|a| a.path == "/test/file1.txt" && matches!(a.content_type, ContentType::Text));
        let has_file2 = attachments
            .iter()
            .any(|a| a.path == "/test/file2.txt" && matches!(a.content_type, ContentType::Text));
        let has_image = attachments
            .iter()
            .any(|a| a.path == "/test/image.png" && matches!(a.content_type, ContentType::Image));

        assert!(has_file1, "Missing file1.txt in attachments");
        assert!(has_file2, "Missing file2.txt in attachments");
        assert!(has_image, "Missing image.png in attachments");
    }

    #[tokio::test]
    async fn test_add_url_with_nonexistent_file() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());
        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with a file that doesn't exist
        let url = "@[/test/nonexistent.txt]".to_string();

        // Execute - Let's handle the error properly
        let result = chat_request.attachments(&url).await;

        // Assert - we expect an error for nonexistent files
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("File not found"));
    }

    #[tokio::test]
    async fn test_add_url_empty() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());
        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with an empty message
        let url = "".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert - no attachments
        assert_eq!(attachments.len(), 0);
    }

    #[tokio::test]
    async fn test_add_url_with_unsupported_extension() {
        // Setup
        let infra = Arc::new(MockInfrastructure::new());

        // Add a file with unsupported extension
        infra.file_service.add_file(
            PathBuf::from("/test/unknown.xyz"),
            "Some content".to_string(),
        );

        let chat_request = ForgeChatRequest::new(infra.clone());

        // Test with the file
        let url = "@[/test/unknown.xyz]".to_string();

        // Execute
        let attachments = chat_request.attachments(&url).await.unwrap();

        // Assert - should be treated as text
        assert_eq!(attachments.len(), 1);
        let attachment = attachments.first().unwrap();
        assert_eq!(attachment.path, "/test/unknown.xyz");
        assert_eq!(attachment.content_type, ContentType::Text);
        assert_eq!(attachment.content, "Some content");
    }
}
