use forge_app::KnowledgeRepository;
use forge_domain::Knowledge;

pub struct ForgeKnowledgeRepository {}

impl Default for ForgeKnowledgeRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeKnowledgeRepository {
    pub fn new() -> Self {
        Self {}
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
