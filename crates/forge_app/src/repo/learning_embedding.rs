use anyhow::Result;
use forge_domain::{Embedding, EmbeddingsRepository, Information};
use uuid::Uuid;

use crate::embeddings::get_embedding;
use crate::rusqlite::SQLConnection;
use crate::sqlite::Sqlite;
use crate::Service;

pub struct Live<P: Sqlite> {
    pool_service: P,
}

impl Service {
    pub async fn learning_embedding_idx(database_url: &str) -> Result<impl EmbeddingsRepository> {
        let db_svc = Service::rusqlite_pool_service(database_url)?;
        Live::new(db_svc).await
    }
}

impl<P: Sqlite<Pool = SQLConnection>> Live<P> {
    pub async fn new(pool_service: P) -> Result<Self> {
        let pool = pool_service.pool().await?;
        let conn = pool.get()?;

        conn.execute_batch(
            "
            CREATE VIRTUAL TABLE IF NOT EXISTS learning_embedding_idx USING vec0(
                id TEXT PRIMARY KEY,
                data TEXT,
                created_at TEXT,
                updated_at TEXT,
                tags TEXT,
                embedding FLOAT[384],
            );
        ",
        )?;

        Ok(Self { pool_service })
    }

    fn row_to_information(row: &rusqlite::Row, distance_idx: Option<usize>) -> Result<Information> {
        let id = Uuid::parse_str(&row.get::<_, String>(0)?)?;
        let created_at = chrono::NaiveDateTime::parse_from_str(
            row.get::<_, String>(2)?.as_str(),
            "%Y-%m-%d %H:%M:%S%.f",
        )?;
        let updated_at = chrono::NaiveDateTime::parse_from_str(
            row.get::<_, String>(3)?.as_str(),
            "%Y-%m-%d %H:%M:%S%.f",
        )?;
        let tags: Vec<String> = serde_json::from_str(&row.get::<_, String>(4)?)?;
        let embedding_bytes = row.get::<_, Vec<u8>>(5)?;
        let embedding_vec = bytes_to_vec(&embedding_bytes)?;

        Ok(Information {
            id,
            data: row.get::<_, String>(1)?,
            embedding: Embedding::new(embedding_vec),
            created_at,
            updated_at,
            tags,
            distance: distance_idx.map(|idx| row.get::<_, f32>(idx).unwrap()),
        })
    }
}

unsafe impl<P: Send + Sync + Sqlite> Send for Live<P> {}
unsafe impl<P: Send + Sync + Sqlite> Sync for Live<P> {}

#[async_trait::async_trait]
impl<P: Send + Sync + Sqlite<Pool = SQLConnection>> EmbeddingsRepository for Live<P> {
    async fn get(&self, id: Uuid) -> Result<Option<Information>> {
        let pool = self.pool_service.pool().await?;
        let conn = pool.get()?;

        let id_str = id.to_string();
        let mut stmt = conn.prepare(
            "
            SELECT id, data, created_at, updated_at, tags, embedding
            FROM learning_embedding_idx
            WHERE id = ?1
            ",
        )?;

        let mut rows = stmt.query(rusqlite::params![id_str])?;
        Ok(rows
            .next()?
            .map(|row| Self::row_to_information(row, None))
            .transpose()?)
    }

    async fn insert(&self, data: String, tags: Vec<String>) -> Result<Embedding> {
        let pool = self.pool_service.pool().await?;
        let conn = pool.get()?;

        let id = Uuid::new_v4();
        let now = chrono::Local::now().naive_local();
        let embedding_vec = get_embedding(data.clone())?;
        let embedding = Embedding::new(embedding_vec);
        let embedding_bytes = vec_to_bytes(embedding.as_slice());
        let tags_json = serde_json::to_string(&tags)?;

        conn.execute(
            "
            INSERT INTO learning_embedding_idx (id, data, created_at, updated_at, tags, embedding)
            VALUES (?1, ?2, ?3, ?4, ?5, ?6)
            ",
            rusqlite::params![
                id.to_string(),
                data,
                now.to_string(),
                now.to_string(),
                tags_json,
                embedding_bytes,
            ],
        )?;

        Ok(embedding)
    }

    async fn search(
        &self,
        embedding: Embedding,
        tags: Vec<String>,
        k: usize,
    ) -> Result<Vec<Information>> {
        let pool = self.pool_service.pool().await?;
        let conn = pool.get()?;

        let query_embedding = vec_to_bytes(embedding.as_slice());

        // Build query based on whether tags are provided,
        // TODO: simplify this logic.
        let mut stmt = if tags.is_empty() {
            conn.prepare(
                "
                SELECT le.id, le.data, le.created_at, le.updated_at, le.tags, le.embedding, distance
                FROM learning_embedding_idx le
                WHERE embedding MATCH ?
                AND k = ?
                ORDER BY distance ASC
                ",
            )?
        } else {
            conn.prepare(
                "
                SELECT le.id, le.data, le.created_at, le.updated_at, le.tags, le.embedding, distance
                FROM learning_embedding_idx le
                WHERE embedding MATCH ?
                AND k = ?
                AND EXISTS (
                    SELECT 1 
                    FROM json_each(le.tags) t
                    WHERE t.value IN (SELECT value FROM json_each(?))
                )
                ORDER BY distance ASC
                ",
            )?
        };

        let mut rows = if tags.is_empty() {
            stmt.query(rusqlite::params![query_embedding, k])?
        } else {
            let tags_json = serde_json::to_string(&tags)?;
            stmt.query(rusqlite::params![query_embedding, k, tags_json])?
        };

        let mut results = Vec::with_capacity(k);
        while let Some(row) = rows.next()? {
            results.push(Self::row_to_information(row, Some(6))?);
        }

        Ok(results)
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
mod tests {
    use super::*;
    use crate::rusqlite::tests::TestSqlite;

    async fn setup_db() -> impl EmbeddingsRepository {
        Live::new(TestSqlite::new().unwrap()).await.unwrap()
    }

    #[tokio::test]
    async fn test_insertion() {
        let repo = setup_db().await;
        let data = "learning about vector indexing".to_string();
        let tags = vec!["learning".to_owned()];
        let result = repo.insert(data, tags).await;
        assert!(result.is_ok());
        assert!(result.unwrap().as_slice().len() == 384);
    }

    // #[tokio::test]
    // async fn test_get() {
    //     let repo = setup_db().await;
    //     let data = "learning about vector indexing".to_string();
    //     let tags = vec!["learning".to_owned()];
    //     let embedding = repo.insert(data.clone(), tags.clone()).await.unwrap();
    //     assert!(embedding.as_slice().len() > 0);

    //     // Get the ID from the database
    //     let mut stmt = repo
    //         .connection
    //         .prepare("SELECT id FROM learning_embedding_idx WHERE data = ?1")
    //         .unwrap();
    //     let id: String = stmt.query_row([data.clone()], |row|
    // row.get(0)).unwrap();     let uuid = Uuid::parse_str(&id).unwrap();

    //     // Try to get the data back
    //     let result = repo.get(uuid).await.unwrap();
    //     assert!(result.is_some());

    //     let info = result.unwrap();
    //     assert_eq!(info.id, uuid);
    //     assert_eq!(info.data, data);
    //     assert_eq!(info.tags, tags);
    //     assert_eq!(info.embedding.as_slice(), embedding.as_slice());
    // }

    #[tokio::test]
    async fn test_search() {
        let repo = setup_db().await;

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
        assert!(results[0].data.contains("cooking")); // Should match cooking
                                                      // recipes since it has
                                                      // "food" tag
    }
}
