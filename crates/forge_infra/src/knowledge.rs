use chrono::{DateTime, NaiveDateTime};
use forge_app::InformationRepository;
use forge_domain::{self as domain};

pub struct ForgeKnowledgeRepository {}

impl ForgeKnowledgeRepository {
    pub fn new() -> Self {
        Self {}
    }
}

struct Knowledge {
    id: i32,
    content: String,
    encoding: Vec<u8>,
    created_at: NaiveDateTime,
    updated_at: NaiveDateTime,
}

struct CreateKnowledge {
    content: String,
    encoding: Vec<u8>,
    created_at: NaiveDateTime,
    updated_at: NaiveDateTime,
}

#[async_trait::async_trait]
impl InformationRepository for ForgeKnowledgeRepository {
    async fn insert(&self, content: &str, embedding: &[f32]) -> anyhow::Result<()> {
        todo!()
    }

    async fn search(&self, embedding: Vec<f32>) -> anyhow::Result<Vec<domain::Knowledge>> {
        todo!()
    }

    async fn list(&self) -> anyhow::Result<Vec<domain::Knowledge>> {
        todo!()
    }
}
