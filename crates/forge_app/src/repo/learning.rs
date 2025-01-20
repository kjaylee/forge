use std::sync::{Arc, Mutex};

use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::prelude::*;
use diesel::sql_types::{Text, Timestamp};
use forge_domain::{Learning, LearningId, LearningRepository};

use crate::embeddings;
use crate::learning_index::LearningIndexBuilder;
use crate::schema::learning_table;
use crate::service::Service;
use crate::sqlite::Sqlite;

#[derive(Debug, Insertable, Queryable, QueryableByName)]
#[diesel(table_name = learning_table)]
struct RawLearning {
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Text)]
    cwd: String,
    #[diesel(sql_type = Text)]
    learnings: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
}

impl TryFrom<RawLearning> for Learning {
    type Error = anyhow::Error;
    fn try_from(raw: RawLearning) -> anyhow::Result<Self> {
        Ok(Learning {
            id: LearningId::parse(&raw.id)?,
            current_working_directory: raw.cwd,
            learnings: serde_json::from_str(&raw.learnings)?,
            created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
            updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
        })
    }
}

use super::super::LearningIndex;

pub struct Live<S> {
    pool_service: S,
    learning_idx: Arc<Mutex<LearningIndex>>,
}

impl<S: Sqlite> Live<S> {
    pub fn new(pool_service: S, learning_idx: Arc<Mutex<LearningIndex>>) -> Self {
        Self { pool_service, learning_idx }
    }
}

#[async_trait::async_trait]
impl<S: Sqlite + Send + Sync> LearningRepository for Live<S> {
    async fn list_learnings(&self) -> anyhow::Result<Vec<Learning>> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;
        let raw_learnings = learning_table::table.load::<RawLearning>(&mut conn)?;
        let learnings = raw_learnings
            .into_iter()
            .map(Learning::try_from)
            .collect::<anyhow::Result<Vec<_>>>()?;
        Ok(learnings)
    }

    async fn recent_learnings(&self, cwd: &str, n: usize) -> anyhow::Result<Vec<Learning>> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;

        let raw_learnings = learning_table::table
            .filter(learning_table::cwd.eq(cwd))
            .order_by(learning_table::updated_at.desc())
            .limit(n as i64)
            .order_by(learning_table::created_at.asc())
            .load::<RawLearning>(&mut conn)?;

        let learnings = raw_learnings
            .into_iter()
            .map(Learning::try_from)
            .collect::<anyhow::Result<Vec<_>>>()?;
        Ok(learnings)
    }

    async fn save(&self, new_learning: Learning) -> anyhow::Result<()> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;

        let raw_learning = RawLearning {
            id: new_learning.id.to_string(),
            cwd: new_learning.current_working_directory.clone(),
            learnings: serde_json::to_string(&new_learning.learnings)?,
            created_at: new_learning.created_at.naive_utc(),
            updated_at: new_learning.updated_at.naive_utc(),
        };

        diesel::insert_into(learning_table::table)
            .values(&raw_learning)
            .execute(&mut conn)?;

        // TODO: use transaction to rollback db insertion if embedding fails
        let learnings = new_learning.learnings.join("\n");
        if let Ok(embedding) = embeddings::get_embedding(learnings) {
            let index = self.learning_idx.lock().unwrap();
            index.add(new_learning.id.to_string(), &embedding)?;
        }

        Ok(())
    }

    async fn search(&self, query: &str, sz: usize) -> anyhow::Result<Vec<Learning>> {
        let embedding = embeddings::get_embedding(query.to_string())?;
        let result = self.learning_idx.lock().unwrap().search(&embedding, sz)?;

        // Now get the pool connection
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;

        // Fetch learnings by IDs
        let mut learnings = Vec::with_capacity(result.len());
        for res in result {
            if let Ok(raw) = learning_table::table
                .find(res.id)
                .first::<RawLearning>(&mut conn)
            {
                if let Ok(learning) = Learning::try_from(raw) {
                    learnings.push(learning);
                }
            }
        }
        Ok(learnings)
    }
}

impl Service {
    pub fn learning_service(database_url: &str) -> anyhow::Result<impl LearningRepository> {
        let pool_service = Service::db_pool_service(database_url)?;
        let learning_index = Arc::new(Mutex::new(
            LearningIndexBuilder::new(database_url)
                .index_name("learning_index")
                .column_name("learning_embedding")
                .vector_size(384 as usize)
                .build()?,
        ));
        Ok(Live::new(pool_service, learning_index))
    }
}

#[cfg(test)]
pub mod tests {
    use std::vec;

    use tempfile::TempDir;

    use super::*;
    use crate::sqlite::tests::TestSqlite;

    pub struct TestStorage;

    impl TestStorage {
        pub fn in_memory() -> anyhow::Result<impl LearningRepository> {
            let pool_service = TestSqlite::new()?;
            let learning_index = Arc::new(Mutex::new(
                LearningIndexBuilder::new(pool_service.path())
                    .index_name("learning_index")
                    .column_name("learning_embedding")
                    .vector_size(384 as usize)
                    .build()?,
            ));
            Ok(Live::new(pool_service, learning_index))
        }
    }

    async fn setup_storage() -> anyhow::Result<impl LearningRepository> {
        TestStorage::in_memory()
    }

    fn test_cwd() -> TempDir {
        TempDir::new().unwrap()
    }

    #[tokio::test]
    async fn test_save_and_retrieve_learnings() {
        let storage = setup_storage().await.unwrap();
        let cwd = test_cwd().path().to_string_lossy().to_string();

        let learning = Learning::new(
            cwd.clone(),
            vec!["test learning 1".to_string(), "test learning 2".to_string()],
        );

        storage.save(learning.clone()).await.unwrap();

        let learnings = storage.list_learnings().await.unwrap();
        assert_eq!(learnings.len(), 1);
        assert_eq!(learnings[0].current_working_directory, cwd);
        assert_eq!(
            learnings[0].learnings,
            vec!["test learning 1", "test learning 2"]
        );
    }

    #[tokio::test]
    async fn test_get_recent_learnings() {
        let storage = setup_storage().await.unwrap();
        for i in 0..5 {
            let cwd = format!("/Users/dir/{}", i);
            let learning = Learning::new(cwd, vec![format!("learning {}", i)]);
            storage.save(learning).await.unwrap();
        }

        let recent = storage.recent_learnings("/Users/dir/1", 3).await.unwrap();
        assert_eq!(recent.len(), 1);
        assert_eq!(recent[0].learnings, vec!["learning 1"]);
    }

    #[tokio::test]
    async fn test_update_existing_learning() {
        let storage = setup_storage().await.unwrap();
        let cwd = test_cwd().path().to_string_lossy().to_string();

        // First learning
        let learning1 = Learning::new(cwd.clone(), vec!["first learning".to_string()]);
        storage.save(learning1.clone()).await.unwrap();

        // Second learning for same directory
        let learning2 = Learning::new(cwd.clone(), vec!["second learning".to_string()]);
        storage.save(learning2).await.unwrap();

        // Verify combined learnings
        let actual = storage.recent_learnings(&cwd, 3).await.unwrap();
        assert_eq!(actual.len(), 2);
        assert_eq!(actual[0].learnings, vec!["first learning"]);
        assert_eq!(actual[1].learnings, vec!["second learning"]);
    }

    #[tokio::test]
    async fn test_return_empty_list_when_recent_learnings_not_present() {
        let storage = setup_storage().await.unwrap();
        let recent = storage
            .recent_learnings("/Users/codeforge", 3)
            .await
            .unwrap();
        assert_eq!(recent.len(), 0);
    }

    #[tokio::test]
    async fn search() {
        let storage = setup_storage().await.unwrap();
        let cwd = test_cwd().path().to_string_lossy().to_string();

        let learning1 = Learning::new(
            cwd.clone(),
            vec![
                "Rust's async/await syntax enables concurrent programming without data races."
                    .to_string(),
                "Tokio provides async primitives like channels and mutexes for safe concurrency."
                    .to_string(),
                "Spawn multiple tasks to handle concurrent operations efficiently.".to_string(),
            ],
        );
        storage.save(learning1).await.unwrap();

        let learning2 = Learning::new(
            cwd.clone(),
            vec![
                "Rust's ownership system and lifetimes ensure thread safety.".to_string(),
                "Send and Sync traits enable safe concurrent data sharing.".to_string(),
                "Arc and Mutex provide thread-safe reference counting and locking.".to_string(),
            ],
        );
        storage.save(learning2).await.unwrap();

        let learning3 = Learning::new(
            cwd.clone(),
            vec![
                "GraphQL schemas define the structure of your API.".to_string(),
                "Query resolvers handle data fetching in GraphQL.".to_string(),
            ],
        );
        storage.save(learning3).await.unwrap();

        let learning4 = Learning::new(
            cwd.clone(),
            vec![
                "Docker images are built using Dockerfiles.".to_string(),
                "Container orchestration manages deployment and scaling.".to_string(),
            ],
        );
        storage.save(learning4).await.unwrap();

        let result = storage
            .search("How do I handle concurrent programming in Rust?", 2)
            .await
            .unwrap();

        assert_eq!(result.len(), 2);
        assert!(result[0]
            .learnings
            .iter()
            .any(|s| s.contains("async/await")));
        assert!(result[1]
            .learnings
            .iter()
            .any(|s| s.contains("thread safety")));
    }
}
