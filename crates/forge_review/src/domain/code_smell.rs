use std::{path::PathBuf, sync::Arc};

use crate::domain::PullRequest;

use super::SummaryAgent;

pub struct CodeSmellAgent {
    review: Arc<PullRequest>,
    file: PathBuf,
}

impl CodeSmellAgent {
    pub fn new(review: Arc<PullRequest>, file: PathBuf) -> Self {
        Self { review, file }
    }
}

#[async_trait::async_trait]
impl SummaryAgent for CodeSmellAgent {
    async fn summarize(&self) -> anyhow::Result<String> {
        todo!()
    }
}