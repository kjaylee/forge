use std::sync::Arc;

use anyhow::Result;
use forge_api::API;

use crate::domain::{PullRequest, RuleList};

#[async_trait::async_trait]
pub trait GithubAPI {
    async fn get_pull_request(&self) -> Result<PullRequest>;
}

#[async_trait::async_trait]
pub trait ProjectRules: Send + Sync {
    async fn rules(&self) -> Result<RuleList>;
}

#[async_trait::async_trait]
pub trait Config: Send + Sync {
    async fn get(&self, key: &str) -> Result<String>;
}

pub trait TemplateRender {
    fn render<T: serde::Serialize>(&self, template: &str, context: T) -> Result<String>;
}

#[async_trait::async_trait]
pub trait ReviewInfrastructure: Send + Sync {
    type GithubAPI: GithubAPI;
    type ArchitectureRules: ProjectRules;
    type CodeSmellRules: ProjectRules;
    type API: API;
    type Config: Config;
    type TemplateRender: TemplateRender;

    fn github_api(&self) -> Arc<Self::GithubAPI>;
    fn architecture_rules(&self) -> Arc<Self::ArchitectureRules>;
    fn code_smell_rules(&self) -> Arc<Self::CodeSmellRules>;
    fn forge_workflow(&self) -> Arc<Self::API>;
    fn config(&self) -> Arc<Self::Config>;
    fn template_renderer(&self) -> Arc<Self::TemplateRender>;
}
