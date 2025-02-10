use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use forge_domain::{
    ChatRequest, EmbeddingsRepository, Environment, FileReadService, ProviderService,
    SystemContext, ToolService,
};
use forge_walker::Walker;
use tracing::debug;

use super::{PromptService, Service};
use crate::{embeddings::Embedder, prompts::Prompt};

const LEARNINGS: usize = 3;

impl Service {
    pub fn system_prompt(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
        file_read: Arc<dyn FileReadService>,
        embedding_repo: Arc<dyn EmbeddingsRepository>,
        system_prompt_path: Option<PathBuf>,
    ) -> impl PromptService {
        Live::new(
            env,
            tool,
            provider,
            file_read,
            embedding_repo,
            system_prompt_path,
        )
    }
}

#[derive(Clone)]
struct Live {
    env: Environment,
    tool: Arc<dyn ToolService>,
    provider: Arc<dyn ProviderService>,
    file_read: Arc<dyn FileReadService>,
    embedding_repo: Arc<dyn EmbeddingsRepository>,
    system_prompt_path: Option<PathBuf>,
}

impl Live {
    pub fn new(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
        file_read: Arc<dyn FileReadService>,
        embedding_repo: Arc<dyn EmbeddingsRepository>,
        system_prompt_path: Option<PathBuf>,
    ) -> Self {
        Self {
            env,
            tool,
            provider,
            file_read,
            system_prompt_path,
            embedding_repo,
        }
    }
}

#[async_trait::async_trait]
impl PromptService for Live {
    async fn get(&self, request: &ChatRequest) -> Result<String> {
        let custom_instructions = match request.custom_instructions {
            None => None,
            Some(ref path) => {
                let content = self.file_read.read(path.clone()).await.unwrap();
                Some(content)
            }
        };

        let tool_supported = self
            .provider
            .parameters(&request.model)
            .await?
            .tool_supported;

        debug!(
            "Tool support for {}: {}",
            request.model.as_str(),
            tool_supported
        );

        let mut files = Walker::max_all()
            .max_depth(2)
            .cwd(self.env.cwd.clone())
            .get()
            .await?
            .iter()
            .map(|f| f.path.to_string())
            .collect::<Vec<_>>();

        // Sort the files alphabetically to ensure consistent ordering
        files.sort();

        let learnings = self
            .embedding_repo
            .search(
                Embedder::new(self.env.cache_dir()).embed(request.content.clone())?,
                vec!["learning".to_owned()],
                LEARNINGS,
            )
            .await?;
        let learnings = if learnings.is_empty() {
            None
        } else {
            Some(learnings.into_iter().map(|l| l.data).collect())
        };

        let ctx = SystemContext {
            env: Some(self.env.clone()),
            tool_information: Some(self.tool.usage_prompt()),
            tool_supported: Some(tool_supported),
            custom_instructions,
            files,
            learnings,
        };

        let prompt = if let Some(path) = self.system_prompt_path.clone() {
            self.file_read.read(path).await?
        } else {
            include_str!("../prompts/coding/system.md").to_owned()
        };
        let prompt = Prompt::new(prompt);
        Ok(prompt.render(&ctx)?)
    }
}

#[cfg(test)]
mod tests {

    use std::path::PathBuf;

    use forge_domain::{EmbeddingsRepository, ModelId, Parameters};
    use insta::assert_snapshot;
    use tempfile::TempDir;
    use tokio::fs;

    use super::*;
    use crate::repo::test::EmbeddingRepositoryTest;
    use crate::service::test::{TestFileReadService, TestProvider};

    async fn test_env(dir: PathBuf) -> Environment {
        let path = dir.display().to_string();
        fs::write(dir.join("file1.txt"), "A").await.unwrap();
        fs::write(dir.join("file2.txt"), "B").await.unwrap();
        fs::create_dir_all(dir.join("nested")).await.unwrap();
        fs::write(dir.join("nested").join("file3.txt"), "B")
            .await
            .unwrap();

        let env = Environment {
            os: "linux".to_string(),
            cwd: dir,
            shell: "/bin/bash".to_string(),
            api_key: "test".to_string(),
            large_model_id: "open-ai/gpt-4o".to_string(),
            small_model_id: "open-ai/gpt-4o-mini".to_string(),
            base_path: PathBuf::from(path),
            home: Some(PathBuf::from("/home/user")),
        };

        fs::create_dir_all(env.cache_dir()).await.unwrap();

        env
    }

    #[tokio::test]
    async fn test_tool_supported() {
        let dir = TempDir::new().unwrap();
        let env = test_env(dir.path().to_path_buf()).await;

        // setup of embedding repository, add some examples in repo.
        let embedding_repo = Arc::new(EmbeddingRepositoryTest::init());
        let _ = embedding_repo
            .insert(
                "Always write unit tests to ensure the correctness of solution".to_string(),
                vec!["learning".to_owned()],
            )
            .await
            .unwrap();
        let _ = embedding_repo
            .insert(
                "with rust always use pattern matching for exhuastive matching".to_string(),
                vec!["learning".to_owned()],
            )
            .await
            .unwrap();

        let tools = Arc::new(Service::tool_service(&env, embedding_repo.clone()));
        let provider = Arc::new(
            TestProvider::default()
                .parameters(vec![(ModelId::new("gpt-3.5-turbo"), Parameters::new(true))]),
        );
        let file = Arc::new(TestFileReadService::default());
        let request = ChatRequest::new(ModelId::new("gpt-3.5-turbo"), "test task");
        let prompt = Live::new(env, tools, provider, file, embedding_repo, None)
            .get(&request)
            .await
            .unwrap()
            .replace(&dir.path().display().to_string(), "[TEMP_DIR]");

        assert_snapshot!(prompt);
    }

    #[tokio::test]
    async fn test_tool_unsupported() {
        let dir = TempDir::new().unwrap();
        let env = test_env(dir.path().to_path_buf()).await;
        let embedding_repo = Arc::new(EmbeddingRepositoryTest::init());
        let tools = Arc::new(Service::tool_service(&env, embedding_repo.clone()));
        let provider = Arc::new(TestProvider::default().parameters(vec![(
            ModelId::new("gpt-3.5-turbo"),
            Parameters::new(false),
        )]));
        let file = Arc::new(TestFileReadService::default());
        let request = ChatRequest::new(ModelId::new("gpt-3.5-turbo"), "test task");
        let prompt = Live::new(env, tools, provider, file, embedding_repo, None)
            .get(&request)
            .await
            .unwrap()
            .replace(&dir.path().display().to_string(), "[TEMP_DIR]");
        assert_snapshot!(prompt);
    }

    #[tokio::test]
    async fn test_system_prompt_custom_prompt() {
        let dir = TempDir::new().unwrap();
        let env = test_env(dir.path().to_path_buf()).await;
        let embedding_repo = Arc::new(EmbeddingRepositoryTest::init());
        let tools = Arc::new(Service::tool_service(&env, embedding_repo.clone()));
        let provider = Arc::new(TestProvider::default().parameters(vec![(
            ModelId::new("gpt-3.5-turbo"),
            Parameters::new(false),
        )]));
        let file = Arc::new(TestFileReadService::default().add(".custom.md", "Woof woof!"));
        let request = ChatRequest::new(ModelId::new("gpt-3.5-turbo"), "test task")
            .custom_instructions(".custom.md");
        let prompt = Live::new(env, tools, provider, file, embedding_repo, None)
            .get(&request)
            .await
            .unwrap()
            .replace(&dir.path().display().to_string(), "[TEMP_DIR]");
        assert!(prompt.contains("Woof woof!"));
    }

    #[tokio::test]
    async fn test_system_prompt_file_path() {
        let dir = TempDir::new().unwrap();
        let env = test_env(dir.path().to_path_buf()).await;
        let embedding_repo = Arc::new(EmbeddingRepositoryTest::init());
        let tools = Arc::new(Service::tool_service(&env, embedding_repo.clone()));
        let provider = Arc::new(TestProvider::default().parameters(vec![(
            ModelId::new("gpt-3.5-turbo"),
            Parameters::new(false),
        )]));
        let file = Arc::new(TestFileReadService::default().add(
            "./custom_system_prompt.md",
            "You're expert at solving puzzles!",
        ));
        let request = ChatRequest::new(ModelId::new("gpt-3.5-turbo"), "test task");
        let prompt = Live::new(
            env,
            tools,
            provider,
            file,
            embedding_repo,
            Some(PathBuf::from("./custom_system_prompt.md")),
        )
        .get(&request)
        .await
        .unwrap();
        assert_eq!(prompt, "You're expert at solving puzzles!");
    }
}
