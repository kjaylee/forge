use std::sync::Arc;

use super::SummaryAgent;
use crate::domain::PullRequest;

pub struct CombineSummaryAgent {
    pull_request: Arc<PullRequest>,
    summary: Vec<String>,
}

impl CombineSummaryAgent {
    pub fn new(pull_request: Arc<PullRequest>, summary: Vec<String>) -> Self {
        Self { pull_request, summary }
    }
}

#[async_trait::async_trait]
impl SummaryAgent for CombineSummaryAgent {
    async fn summarize(&self) -> anyhow::Result<String> {
        todo!()
    }
}
