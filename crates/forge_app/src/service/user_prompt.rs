use std::sync::Arc;

use anyhow::{Context as _, Result};
use forge_domain::{ChatRequest, FileReadService};
use forge_prompt::Prompt;
use handlebars::Handlebars;
use serde::Serialize;

use super::{PromptService, Service};

impl Service {
    pub fn user_prompt_service(file_read: Arc<dyn FileReadService>) -> impl PromptService {
        Live { file_read }
    }
}

struct Live {
    file_read: Arc<dyn FileReadService>,
}

#[derive(Serialize)]
struct PromptContext {
    task: String,
    files: Vec<FileRead>,
}

#[derive(Serialize)]
struct FileRead {
    path: String,
    content: String,
}

#[async_trait::async_trait]
impl PromptService for Live {
    async fn get(&self, request: &ChatRequest) -> Result<String> {
        let template = include_str!("../prompts/coding/user_task.md");
        let parsed_task = Prompt::parse(request.content.to_string());

        let mut file_contents = vec![];
        for file_path in parsed_task.files() {
            let content = self
                .file_read
                .read(file_path.clone().into())
                .await
                .with_context(|| format!("Failed to read content from file: {}", file_path))?;
            file_contents.push(FileRead { path: file_path, content });
        }

        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        let ctx = PromptContext { task: request.content.to_string(), files: file_contents };

        Ok(hb
            .render_template(template, &ctx)
            .with_context(|| "Failed to render user task template")?)
    }
}

#[cfg(test)]
pub mod tests {

    use tempfile::TempDir;

    use super::*;
    use crate::service::test::TestFileReadService;


    #[tokio::test]
    async fn test_render_user_prompt() {
        // Create a temp directory and write some files in it.
        let temp_dir = TempDir::new().unwrap();
        let foo_path = temp_dir
            .path()
            .join("foo.txt")
            .to_string_lossy()
            .to_string();
        let bar_path = temp_dir
            .path()
            .join("bar.txt")
            .to_string_lossy()
            .to_string();
        tokio::fs::write(&foo_path, "Hello World - Foo")
            .await
            .unwrap();
        tokio::fs::write(&bar_path, "Hello World - Bar")
            .await
            .unwrap();

        let file_read = Arc::new(
            TestFileReadService::default()
                .add(&foo_path, "Hello World - Foo")
                .add(&bar_path, "Hello World - Bar"),
        );
        let request = ChatRequest::new(
            forge_domain::ModelId::new("gpt-3.5-turbo"),
            format!(
                "read this file content from @{} and @{}",
                &foo_path, &bar_path
            ),
        );
        let rendered_prompt = Service::user_prompt_service(file_read)
            .get(&request)
            .await
            .unwrap();

        // since temp path keep on changing, we need to replace it with static path.
        let rendered_prompt = rendered_prompt
            .replace(&foo_path, "foo.txt")
            .replace(&bar_path, "bar.txt");

        insta::assert_snapshot!(rendered_prompt);
    }
}
