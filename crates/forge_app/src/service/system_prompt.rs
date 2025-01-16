use std::sync::Arc;
use std::collections::HashSet;

use anyhow::Result;
use forge_domain::{Environment, LearningRepository, ModelId, ProviderService};
use handlebars::Handlebars;
use serde::Serialize;
use tracing::debug;

use super::tool_service::ToolService;
use super::Service;

// Number of recent learnings to show in the prompt
const RECENT_LEARNING_COUNT: usize = 5;

#[async_trait::async_trait]
pub trait SystemPromptService: Send + Sync {
    async fn get_system_prompt(&self, model: &ModelId) -> Result<String>;
}

impl Service {
    pub fn system_prompt(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
        learning_repository: Arc<dyn LearningRepository>,
    ) -> impl SystemPromptService {
        Live::new(env, tool, provider, learning_repository)
    }
}

#[derive(Clone, Serialize)]
struct Context {
    env: Environment,
    tool_information: String,
    tool_supported: bool,
    learnings: Option<Vec<String>>,
}

#[derive(Clone)]
struct Live {
    env: Environment,
    tool: Arc<dyn ToolService>,
    provider: Arc<dyn ProviderService>,
    learning_repository: Arc<dyn LearningRepository>,
}

impl Live {
    pub fn new(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
        learning_repository: Arc<dyn LearningRepository>,
    ) -> Self {
        Self { env, tool, provider, learning_repository }
    }
}

#[async_trait::async_trait]
impl SystemPromptService for Live {
    async fn get_system_prompt(&self, model: &ModelId) -> Result<String> {
        let template = include_str!("../prompts/coding/system.md");

        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        let tool_supported = self.provider.parameters(model).await?.tool_supported;
        debug!("Tool support for {}: {}", model.as_str(), tool_supported);

        let learnings = self
            .learning_repository
            .recent_learnings(&self.env.cwd, RECENT_LEARNING_COUNT)
            .await
            .ok()
            .and_then(|recent_learnings| {
                let mut seen = HashSet::with_capacity(recent_learnings.len());
                let mut learnings = recent_learnings
                    .into_iter()
                    .flat_map(|l| l.learnings)
                    .collect::<Vec<_>>();
                // dedupe learnings if there are any duplicates to save tokens.
                learnings.retain(|x| seen.insert(x.clone()));
                Some(learnings)
            });

        let ctx = Context {
            env: self.env.clone(),
            tool_information: self.tool.usage_prompt(),
            tool_supported,
            learnings,
        };

        Ok(hb.render_template(template, &ctx)?)
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::{Learning, Parameters};
    use insta::assert_snapshot;

    use super::*;
    use crate::service::tests::TestProvider;
    use crate::tests::TestLearningStorage;

    fn test_env() -> Environment {
        Environment {
            os: "linux".to_string(),
            cwd: "/home/user/project".to_string(),
            shell: "/bin/bash".to_string(),
            home: Some("/home/user".to_string()),
            files: vec!["file1.txt".to_string(), "file2.txt".to_string()],
            api_key: "test".to_string(),
            large_model_id: "open-ai/gpt-4o".to_string(),
            small_model_id: "open-ai/gpt-4o-mini".to_string(),
        }
    }

    #[tokio::test]
    async fn test_tool_supported() {
        let env = test_env();
        let learning_repository = Arc::new(TestLearningStorage::in_memory().unwrap());
        let tools = Arc::new(Service::tool_service(
            env.cwd.clone(),
            learning_repository.clone(),
        ));
        let provider = Arc::new(
            TestProvider::default().parameters(vec![(ModelId::default(), Parameters::new(true))]),
        );
        let prompt = Live::new(env, tools, provider, learning_repository)
            .get_system_prompt(&ModelId::default())
            .await
            .unwrap();
        assert_snapshot!(prompt);
    }

    #[tokio::test]
    async fn test_tool_unsupported() {
        let env = test_env();
        let learning_repository = Arc::new(TestLearningStorage::in_memory().unwrap());
        let tools = Arc::new(Service::tool_service(
            env.cwd.clone(),
            learning_repository.clone(),
        ));
        let provider = Arc::new(
            TestProvider::default().parameters(vec![(ModelId::default(), Parameters::new(false))]),
        );
        let prompt = Live::new(env, tools, provider, learning_repository)
            .get_system_prompt(&ModelId::default())
            .await
            .unwrap();
        assert_snapshot!(prompt);
    }

    #[tokio::test]
    async fn test_render_recent_learnings_when_present() {
        let env = test_env();
        let learning_repository = Arc::new(TestLearningStorage::in_memory().unwrap());

        learning_repository
            .save(Learning::new(
                env.cwd.clone(),
                vec!["Always write unit tests to ensure the correctness.".to_string(),
                 "Once the task is complete, run tests to ensure the changes are correctly integrated.".to_string()],
            ))
            .await
            .unwrap();

        learning_repository
            .save(Learning::new(
                env.cwd.clone(),
                vec![
                    "Avoid Hardcoding things in the code.".to_string(),
                    "Always write unit tests to ensure the correctness.".to_string(),
                ],
            ))
            .await
            .unwrap();

        let tools = Arc::new(Service::tool_service(
            env.cwd.clone(),
            learning_repository.clone(),
        ));
        let provider = Arc::new(
            TestProvider::default().parameters(vec![(ModelId::default(), Parameters::new(true))]),
        );

        let prompt = Live::new(env, tools, provider, learning_repository)
            .get_system_prompt(&ModelId::default())
            .await
            .unwrap();
        insta::assert_snapshot!(prompt);
    }
}
