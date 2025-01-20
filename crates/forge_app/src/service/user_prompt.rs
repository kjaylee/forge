use std::sync::Arc;

use anyhow::Result;
use forge_domain::IdeRepository;
use forge_prompt::Prompt;
use handlebars::Handlebars;
use serde::Serialize;

use super::file_read::FileReadService;
use super::Service;

#[async_trait::async_trait]
pub trait UserPromptService: Send + Sync {
    async fn get_user_prompt(&self, task: &str) -> Result<String>;
}

impl Service {
    pub fn user_prompt_service(
        file_read: Arc<dyn FileReadService>,
        all_ides: Arc<dyn IdeRepository>,
    ) -> impl UserPromptService {
        Live { file_read, all_ides }
    }
}

struct Live {
    file_read: Arc<dyn FileReadService>,
    all_ides: Arc<dyn IdeRepository>,
}

#[derive(Serialize)]
struct Context {
    task: String,
    files: Vec<FileRead>,
}

#[derive(Serialize)]
struct FileRead {
    path: String,
    content: String,
}

#[async_trait::async_trait]
impl UserPromptService for Live {
    async fn get_user_prompt(&self, task: &str) -> Result<String> {
        let template = include_str!("../prompts/coding/user_task.md");
        let parsed_task = Prompt::parse(task.to_string());

        let mut file_contents = vec![];
        for file in parsed_task.files() {
            let content = self.file_read.read(file.clone()).await?;
            file_contents.push(FileRead { path: file, content });
        }

        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        let ctx = Context { task: task.to_string(), files: file_contents };
        let mut ans = hb.render_template(template, &ctx)?;
        if let Ok(ides) = self.all_ides.get_active_ides().await {
            for ide in ides {
                if let Ok(workspace) = self.all_ides.get_workspace(&ide.workspace_id).await {
                    ans.push_str("Focused File:\n");
                    ans.push_str(&workspace.focused_file_xml(&ide.name));

                    ans.push_str("\nOpened Files:\n");
                    ans.push_str(&workspace.opened_files_xml(&ide.name));
                }
            }
        }

        Ok(ans)
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;

    use async_trait::async_trait;
    use forge_domain::{Ide, Workspace, WorkspaceId};

    use super::*;
    use crate::service::file_read::tests::TestFileReadService;

    pub struct TestUserPrompt;

    #[async_trait::async_trait]
    impl UserPromptService for TestUserPrompt {
        async fn get_user_prompt(&self, task: &str) -> Result<String> {
            Ok(format!("<task>{}</task>", task))
        }
    }

    struct MockIdeRepository;

    #[async_trait]
    impl IdeRepository for MockIdeRepository {
        async fn get_active_ides(&self) -> Result<Vec<Ide>> {
            Ok(vec![])
        }

        async fn get_workspace(&self, _: &WorkspaceId) -> Result<Workspace> {
            Ok(Workspace::default())
        }
    }

    #[tokio::test]
    async fn test_render_user_prompt() {
        let mut file_map = HashMap::new();
        file_map.insert("foo.txt".to_string(), "Hello World - Foo".to_string());
        file_map.insert("bar.txt".to_string(), "Hello World - Bar".to_string());

        let file_read = Arc::new(TestFileReadService::new(file_map));
        let rendered_prompt = Service::user_prompt_service(file_read, Arc::new(MockIdeRepository))
            .get_user_prompt("read this file content from @foo.txt and @bar.txt")
            .await
            .unwrap();
        insta::assert_snapshot!(rendered_prompt);
    }
}
