use chrono::NaiveDateTime;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct Embedding(Vec<f32>);

impl Embedding {
    pub fn new(embedding: Vec<f32>) -> Self {
        Self(embedding)
    }
    pub fn as_slice(&self) -> &[f32] {
        &self.0
    }
}
pub struct Information {
    pub data: String,
    pub id: Uuid,
    pub embedding: Embedding,
    pub created_at: NaiveDateTime,
    pub updated_at: NaiveDateTime,
    pub tags: Vec<String>,
    pub distance: Option<f32>,
}

#[async_trait::async_trait]
pub trait EmbeddingsRepository {
    async fn get(&self, id: Uuid) -> anyhow::Result<Option<Information>>;

    async fn insert(&self, bytes: String, tags: Vec<String>) -> anyhow::Result<Embedding>;
    async fn search(
        &self,
        embedding: Embedding,
        tags: Vec<String>,
        k: usize,
    ) -> anyhow::Result<Vec<Information>>;
}
