use anyhow::Result;
use forge_api::API;

use crate::domain::{PullRequest, RuleList};

#[async_trait::async_trait]
pub trait GithubAPI {
    async fn get_pull_request(&self) -> Result<PullRequest>;
}

#[async_trait::async_trait]
pub trait ProjectRules {
    async fn rules(&self) -> Result<RuleList>;
}

#[async_trait::async_trait]
pub trait Config {
    async fn get(&self, key: &str) -> Result<String>;
}

pub trait TemplateRender {
    fn render<T: serde::Serialize>(&self, template: &str, context: T) -> Result<String>;
}

#[async_trait::async_trait]
pub trait ReviewInfrastructure: Send + Sync {
    type GithubAPI: GithubAPI;
    type ProjectRules: ProjectRules;
    type API: API;
    type Config: Config;
    type TemplateRender: TemplateRender;

    fn github_api(&self) -> &Self::GithubAPI;
    fn project_rules(&self) -> &Self::ProjectRules;
    fn forge_workflow(&self) -> &Self::API;
    fn config(&self) -> &Self::Config;
    fn template_renderer(&self) -> &Self::TemplateRender;
}
