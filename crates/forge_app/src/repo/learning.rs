use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::prelude::*;
use diesel::sql_types::{Text, Timestamp};
use forge_domain::{Learning, LearningId, LearningRepository};

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
        let raw_learnings = learning_table::table.load::<RawLearning>(&mut conn)?;
        let learnings: Vec<Learning> = raw_learnings
            .into_iter()
            .map(|raw_learning| Learning::try_from(raw_learning))
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
            .load::<RawLearning>(&mut conn)?;

        let mut learnings: Vec<Learning> = raw_learnings
            .into_iter()
            .map(|raw_learning| Learning::try_from(raw_learning))
            .collect::<anyhow::Result<Vec<_>>>()?;

        learnings.sort_by(|a, b| a.created_at.cmp(&b.created_at));
        Ok(learnings)
    }

    async fn save(&self, new_learning: Learning) -> anyhow::Result<()> {
        let pool = self
            .pool_service
            .pool()
            .await
            .map_err(|e| anyhow::anyhow!(e))?;
        let mut conn = pool.get().map_err(|e| anyhow::anyhow!(e))?;

        let raw = RawLearning {
            id: new_learning.id.to_string(),
            cwd: new_learning.current_working_directory,
            learnings: serde_json::to_string(&new_learning.learnings)?,
            created_at: new_learning.created_at.naive_utc(),
            updated_at: new_learning.updated_at.naive_utc(),
        };

        diesel::insert_into(learning_table::table)
            .values(&raw)
            .execute(&mut conn)?;

        Ok(())
    }
}

impl Service {
    pub fn learning_service(database_url: &str) -> anyhow::Result<impl LearningRepository> {
        let pool_service = Service::db_pool_service(database_url)?;
        Ok(Live::new(pool_service))
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
            Ok(Live::new(pool_service))
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
}
