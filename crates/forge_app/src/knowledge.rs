use std::sync::Arc;

use forge_domain::{Knowledge, KnowledgeService, Query};


pub struct ForgeKnowledgeService {}
impl ForgeKnowledgeService {
    pub fn new<F>(infra: Arc<F>) -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl KnowledgeService for ForgeKnowledgeService {
    async fn search(&self, query: Query) -> anyhow::Result<Vec<Knowledge>> {
        todo!()
    }

    async fn store(&self, content: &str) -> anyhow::Result<()> {
        todo!()
    }

    async fn list(&self) -> anyhow::Result<Vec<Knowledge>> {
        todo!()
    }
}
