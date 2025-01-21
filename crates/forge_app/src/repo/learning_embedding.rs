use anyhow::Result;
use chrono::NaiveDateTime;
use diesel::prelude::*;
use diesel::sql_types::{Binary, Float, Text, Timestamp};
use forge_domain::{Embedding, EmbeddingsRepository, Information};
use uuid::Uuid;

use crate::embeddings::get_embedding;
use crate::schema::learning_embedding_idx;
use crate::sqlite::Sqlite;
use crate::Service;

#[derive(Queryable, Insertable, QueryableByName)]
#[diesel(table_name = learning_embedding_idx)]
struct LearningEmbedding {
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Text)]
    data: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
    #[diesel(sql_type = Text)]
    tags: String,
    #[diesel(sql_type = Binary)]
    embedding: Vec<u8>,
}

#[derive(QueryableByName)]
struct SearchResult {
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Text)]
    data: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
    #[diesel(sql_type = Text)]
    tags: String,
    #[diesel(sql_type = Binary)]
    embedding: Vec<u8>,
    #[diesel(sql_type = Float)]
    distance: f32,
}

pub struct Live<P: Sqlite> {
    pool_service: P,
}

impl Service {
    pub async fn learning_embedding_idx(database_url: &str) -> Result<impl EmbeddingsRepository> {
        let db_svc = Service::db_pool_service(database_url)?;
        Live::new(db_svc).await
    }
}

impl<P: Sqlite> Live<P> {
    pub async fn new(pool_service: P) -> Result<Self> {
        let pool = pool_service.pool().await?;
        let mut conn = pool.get()?;
        // Create virtual table for vector search
        // TODO: implement custom migration setup that can work with diesel.
        diesel::sql_query(
            "CREATE VIRTUAL TABLE IF NOT EXISTS learning_embedding_idx USING vec0(
                id TEXT PRIMARY KEY,
                data TEXT,
                created_at TEXT,
                updated_at TEXT,
                tags TEXT,
                embedding FLOAT[384]
            );",
        )
        .execute(&mut conn)?;

        Ok(Self { pool_service })
    }
}

impl TryFrom<LearningEmbedding> for Information {
    type Error = anyhow::Error;
    fn try_from(row: LearningEmbedding) -> Result<Self> {
        let id = Uuid::parse_str(&row.id)?;
        let tags: Vec<String> = serde_json::from_str(&row.tags)?;
        let embedding_vec = bytes_to_vec(&row.embedding)?;

        Ok(Information {
            id,
            data: row.data.clone(),
            embedding: Embedding::new(embedding_vec),
            created_at: row.created_at,
            updated_at: row.updated_at,
            tags,
            distance: None,
        })
    }
}

#[async_trait::async_trait]
impl<P: Send + Sync + Sqlite> EmbeddingsRepository for Live<P> {
    async fn get(&self, id: Uuid) -> Result<Option<Information>> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;

        let result = learning_embedding_idx::table
            .filter(learning_embedding_idx::id.eq(id.to_string()))
            .first::<LearningEmbedding>(&mut conn)
            .optional()?;

        Ok(result.map(Information::try_from).transpose()?)
    }

    async fn insert(&self, data: String, tags: Vec<String>) -> Result<Embedding> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;

        let id = Uuid::new_v4();
        let now = chrono::Local::now().naive_local();
        let embedding_vec = get_embedding(data.clone())?;
        let embedding = Embedding::new(embedding_vec);
        let embedding_bytes = vec_to_bytes(embedding.as_slice());
        let tags_json = serde_json::to_string(&tags)?;

        let new_embedding = LearningEmbedding {
            id: id.to_string(),
            data,
            created_at: now,
            updated_at: now,
            tags: tags_json,
            embedding: embedding_bytes,
        };

        diesel::insert_into(learning_embedding_idx::table)
            .values(&new_embedding)
            .execute(&mut conn)?;
        Ok(embedding)
    }

    async fn search(
        &self,
        embedding: Embedding,
        tags: Vec<String>,
        k: usize,
    ) -> Result<Vec<Information>> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;

        let query_embedding = vec_to_bytes(embedding.as_slice());
        let tags_json = serde_json::to_string(&tags)?;

        let results = if tags.is_empty() {
            diesel::sql_query(
                "SELECT id, data, created_at, updated_at, tags, embedding, distance
                FROM learning_embedding_idx
                WHERE embedding MATCH ?
                AND k = ?
                ORDER BY distance ASC",
            )
            .bind::<Binary, _>(query_embedding)
            .bind::<diesel::sql_types::Integer, _>(k as i32)
            .load::<SearchResult>(&mut conn)?
        } else {
            diesel::sql_query(
                "SELECT le.id, le.data, le.created_at, le.updated_at, le.tags, le.embedding, distance
                FROM learning_embedding_idx le
                WHERE embedding MATCH ?
                AND k = ?
                AND EXISTS (
                    SELECT 1 
                    FROM json_each(le.tags) t
                    WHERE t.value IN (SELECT value FROM json_each(?))
                )
                ORDER BY distance ASC"
            )
            .bind::<Binary, _>(query_embedding)
            .bind::<diesel::sql_types::Integer, _>(k as i32)
            .bind::<Text, _>(tags_json)
            .load::<SearchResult>(&mut conn)?
        };

        let mut information = Vec::with_capacity(results.len());
        for result in results {
            let mut embedding = Information::try_from(LearningEmbedding {
                id: result.id,
                data: result.data,
                created_at: result.created_at,
                updated_at: result.updated_at,
                tags: result.tags,
                embedding: result.embedding,
            })?;
            embedding.distance = Some(result.distance);
            information.push(embedding);
        }

        Ok(information)
    }
}

fn vec_to_bytes(v: &[f32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(v.len() * 4);
    for &x in v {
        bytes.extend_from_slice(&x.to_le_bytes());
    }
    bytes
}

fn bytes_to_vec(v: &[u8]) -> Result<Vec<f32>> {
    let mut vec = Vec::with_capacity(v.len() / 4);
    for chunk in v.chunks_exact(4) {
        vec.push(f32::from_le_bytes(chunk.try_into().unwrap()));
    }
    Ok(vec)
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::sqlite::tests::TestSqlite;

    pub struct LearningEmeddingTest;

    impl LearningEmeddingTest {
        pub async fn init() -> impl EmbeddingsRepository {
            Live::new(TestSqlite::new().unwrap()).await.unwrap()
        }
    }

    #[tokio::test]
    async fn test_insertion() {
        let repo = LearningEmeddingTest::init().await;
        let data = "learning about vector indexing".to_string();
        let tags = vec!["learning".to_owned()];
        let result = repo.insert(data, tags).await;
        assert!(result.is_ok());
        assert!(result.unwrap().as_slice().len() == 384);
    }

    #[tokio::test]
    async fn test_search() {
        let repo = LearningEmeddingTest::init().await;

        // Insert some test data
        let data1 = "learning about vector indexing".to_string();
        let data2 = "vector similarity search methods".to_string();
        let data3 = "cooking recipes for pasta".to_string();

        let tags1 = vec!["learning".to_owned(), "vectors".to_owned()];
        let tags2 = vec!["vectors".to_owned(), "search".to_owned()];
        let tags3 = vec!["cooking".to_owned(), "food".to_owned()];

        let embedding1 = repo.insert(data1.clone(), tags1.clone()).await.unwrap();
        repo.insert(data2.clone(), tags2.clone()).await.unwrap();
        repo.insert(data3.clone(), tags3.clone()).await.unwrap();

        // Search using the first embedding
        let results = repo.search(embedding1.clone(), vec![], 2).await.unwrap();
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].data, data1); // Most similar should be itself

        // Search with tags
        let new_search = Embedding::new(get_embedding("i like eating food".to_string()).unwrap());
        let results = repo.search(new_search, vec![], 2).await.unwrap();
        assert!(!results.is_empty());
        assert!(results[0].data.contains("cooking"));
    }

    #[tokio::test]
    async fn test_get() {
        let repo = LearningEmeddingTest::init().await;

        // Insert test data
        let data = "test embedding data".to_string();
        let tags = vec!["test".to_owned(), "data".to_owned()];
        let embedding = repo.insert(data.clone(), tags.clone()).await.unwrap();

        // Get the ID from a search
        let results = repo.search(embedding, vec![], 1).await.unwrap();
        assert_eq!(results.len(), 1);
        let id = results[0].id;

        // Test successful retrieval
        let result = repo.get(id).await.unwrap();
        assert!(result.is_some());
        let info = result.unwrap();
        assert_eq!(info.data, data);
        assert_eq!(info.tags, tags);
        assert_eq!(info.embedding.as_slice().len(), 384);
    }

    #[tokio::test]
    async fn test_comprehensive_search() {
        let repo = LearningEmeddingTest::init().await;
        // Insert multiple learning examples about different topics
        let rust_async = vec![
            "Rust's async/await syntax enables concurrent programming without data races.",
            "Tokio provides async primitives like channels and mutexes for safe concurrency.",
            "Spawn multiple tasks to handle concurrent operations efficiently.",
        ];
        for text in rust_async {
            repo.insert(text.to_string(), vec!["learning".to_owned()])
                .await
                .unwrap();
        }

        let rust_threading = vec![
            "Rust's ownership system and lifetimes ensure thread safety.",
            "Send and Sync traits enable safe concurrent data sharing.",
            "Arc and Mutex provide thread-safe reference counting and locking.",
        ];
        for text in rust_threading {
            repo.insert(text.to_string(), vec!["learning".to_owned()])
                .await
                .unwrap();
        }

        let graphql = vec![
            "GraphQL schemas define the structure of your API.",
            "Query resolvers handle data fetching in GraphQL.",
        ];
        for text in graphql {
            repo.insert(text.to_string(), vec!["learning".to_owned()])
                .await
                .unwrap();
        }

        let docker = vec![
            "Docker images are built using Dockerfiles.",
            "Container orchestration manages deployment and scaling.",
        ];
        for text in docker {
            repo.insert(text.to_string(), vec!["learning".to_owned()])
                .await
                .unwrap();
        }

        // Search with tags
        let query = "Tell me about APIs";
        let query_embedding = Embedding::new(get_embedding(query.to_string()).unwrap());
        let results = repo.search(query_embedding, vec![], 2).await.unwrap();

        // Verify we get GraphQL results when searching with the graphql tag
        assert_eq!(results.len(), 2);
        assert!(results.iter().any(|r| r.data.contains("GraphQL")));
    }
}
