use forge_app::KnowledgeRepository;
use forge_domain::Knowledge;

use crate::conn::ForgeConnection;

pub struct ForgeKnowledgeRepository {
    conn: ForgeConnection,
}

impl ForgeKnowledgeRepository {
    pub fn new(conn: ForgeConnection) -> Self {
        Self { conn }
    }
}

#[async_trait::async_trait]
impl KnowledgeRepository for ForgeKnowledgeRepository {
    async fn insert(&self, content: &str, embedding: &[f32]) -> anyhow::Result<()> {
        todo!()
    }

    async fn search(&self, embedding: Vec<f32>) -> anyhow::Result<Vec<Knowledge>> {
        todo!()
    }

    async fn list(&self) -> anyhow::Result<Vec<Knowledge>> {
        todo!()
    }
}
