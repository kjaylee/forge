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
        let read = self.infra.file_read_service().read(path.as_path()).await?;
        let path = path.to_string_lossy().to_string();
        if let Some(img_extension) = extension.and_then(|ext| match ext.as_str() {
            "jpeg" | "jpg" => Some("jpeg"),
            "png" => Some("png"),
            "webp" => Some("webp"),
            _ => None,
        }) {
            let base_64_encoded = base64::engine::general_purpose::STANDARD.encode(read);
            let content = format!("data:image/{};base64,{}", img_extension, base_64_encoded);
            Ok(Attachment { content, path, content_type: ContentType::Image })
        } else {
            let content = String::from_utf8(read.to_vec())?;
            Ok(Attachment { content, path, content_type: ContentType::Text })
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

    use std::path::Path;
    use std::sync::Arc;

    use base64::Engine;
    use forge_domain::{AttachmentService, ContentType};

    use crate::attachment::ForgeChatRequest;
    use crate::{infra, FsWriteService, Infrastructure};

    #[tokio::test]
    async fn test_add_url_with_text_file() {
        // Setup
        let infra = Arc::new(infra::stub::Stub::default());
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
        let infra = Arc::new(infra::stub::Stub::default());
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
            format!("data:image/png;base64,{}", expected_base64)
        );
    }

    #[tokio::test]
    async fn test_add_url_with_jpg_image_with_spaces() {
        // Setup
        let infra = Arc::new(infra::stub::Stub::default());
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
            format!("data:image/jpeg;base64,{}", expected_base64)
        );
    }

    #[tokio::test]
    async fn test_add_url_with_multiple_files() {
        // Setup
        let infra = Arc::new(infra::stub::Stub::default());

        // Add an extra file to our mock service
        infra
            .file_write_service()
            .write(
                Path::new("/test/file2.txt"),
                "This is another text file".into(),
            )
            .await
            .unwrap();

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
        let infra = Arc::new(infra::stub::Stub::default());
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
        let infra = Arc::new(infra::stub::Stub::default());
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
        let infra = Arc::new(infra::stub::Stub::default());

        // Add a file with unsupported extension
        infra
            .file_write_service()
            .write(Path::new("/test/unknown.xyz"), "Some content".into())
            .await
            .unwrap();

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
