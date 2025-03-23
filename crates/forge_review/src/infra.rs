use crate::domain::PullRequest;

#[async_trait::async_trait]
pub trait ReviewInfrastructure {
    async fn get_pull_request(&self) -> anyhow::Result<PullRequest>;
}
