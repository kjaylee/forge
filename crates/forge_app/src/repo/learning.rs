use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::prelude::*;
use diesel::sql_types::{Text, Timestamp};
use forge_domain::{Learning, LearningId, LearningRepository};

use crate::error::Result;
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
}

impl TryFrom<RawLearning> for Learning {
    type Error = crate::error::Error;
    fn try_from(raw: RawLearning) -> Result<Self> {
        Ok(Learning {
            id: LearningId::parse(&raw.id)?,
            current_working_directory: raw.cwd,
            learnings: serde_json::from_str(&raw.learnings)?,
            created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
        })
    }
}

pub struct Live<S> {
    pool_service: S,
}

impl<S: Sqlite> Live<S> {
    pub fn new(pool_service: S) -> Self {
        Self { pool_service }
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
        let raw_learnings = learning_table::table
            .order_by(learning_table::created_at.desc())
            .load::<RawLearning>(&mut conn)?;

        let mut learnings = Vec::new();
        for learning in raw_learnings {
            let learning: Learning = learning
                .try_into()
                .map_err(|e: crate::Error| anyhow::anyhow!(e))?;
            learnings.push(learning);
        }
        Ok(learnings)
    }

    async fn recent_learnings(&self, n: usize) -> anyhow::Result<Vec<Learning>> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;
        let raw_learnings = learning_table::table
            .order_by(learning_table::created_at.desc())
            .limit(n as i64)
            .load::<RawLearning>(&mut conn)?;

        let mut learnings = Vec::new();
        for learning in raw_learnings {
            let learning: Learning = learning
                .try_into()
                .map_err(|e: crate::Error| anyhow::anyhow!(e))?;
            learnings.push(learning);
        }
        Ok(learnings)
    }

    async fn save(&self, learning: Learning) -> anyhow::Result<()> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;

        let raw = RawLearning {
            id: learning.id.to_string(),
            cwd: learning.current_working_directory.to_string(),
            learnings: serde_json::to_string(&learning.learnings)?,
            created_at: learning.created_at.naive_utc(),
        };

        diesel::insert_into(learning_table::table)
            .values(&raw)
            .execute(&mut conn)?;

        Ok(())
    }
}

impl Service {
    pub fn learning_service(database_url: &str) -> Result<impl LearningRepository> {
        let pool_service = Service::db_pool_service(database_url)?;
        Ok(Live::new(pool_service))
    }
}

#[cfg(test)]
pub mod tests {
    use tempfile::TempDir;

    use super::*;
    use crate::sqlite::tests::TestSqlite;

    pub struct TestStorage;

    impl TestStorage {
        pub fn in_memory() -> Result<impl LearningRepository> {
            let pool_service = TestSqlite::new()?;
            Ok(Live::new(pool_service))
        }
    }

    async fn setup_storage() -> Result<impl LearningRepository> {
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
        let cwd = test_cwd().path().to_string_lossy().to_string();

        for i in 0..5 {
            let learning = Learning::new(cwd.clone(), vec![format!("learning {}", i)]);
            storage.save(learning).await.unwrap();
        }

        let recent = storage.recent_learnings(3).await.unwrap();
        assert_eq!(recent.len(), 3);
        assert_eq!(recent[0].learnings, vec!["learning 4"]);
        assert_eq!(recent[1].learnings, vec!["learning 3"]);
        assert_eq!(recent[2].learnings, vec!["learning 2"]);
    }
}
