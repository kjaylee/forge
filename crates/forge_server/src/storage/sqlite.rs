#![allow(dead_code)]
use std::fmt::Debug;
use std::path::Path;

use serde::de::DeserializeOwned;
use serde::Serialize;
use sqlx::{Row, SqlitePool};
use tracing::info;

use super::{Storage, StorageError};

const DB_PATH: &str = ".codeforge.db";

#[derive(Debug)]
pub struct SqliteStorage {
    pool: SqlitePool,
}

impl SqliteStorage {
    /// Create a new SQLite storage with a custom path
    pub async fn new(db_path: impl AsRef<Path>) -> Result<Self, StorageError> {
        let db_url = format!("sqlite://{}", db_path.as_ref().to_string_lossy());
        let pool = SqlitePool::connect(&db_url).await?;

        let storage = Self { pool };
        storage.init().await?;
        info!("Initialized SQLite database",);
        Ok(storage)
    }

    /// Create a new SQLite storage with the default path
    pub async fn default() -> Result<Self, StorageError> {
        Self::new(Path::new(DB_PATH)).await
    }
}

#[async_trait::async_trait]
impl Storage for SqliteStorage {
    async fn init(&self) -> Result<(), StorageError> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS conversation_history (
                id VARCHAR(36) PRIMARY KEY,
                data TEXT NOT NULL,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
            "#,
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn save<T>(&self, key: &str, item: &T) -> Result<(), StorageError>
    where
        T: Serialize + Send + Sync,
    {
        let json_data = serde_json::to_string(item)?;
        sqlx::query(
            r#"
            INSERT INTO conversation_history (id, data)
            VALUES (?, ?)
            ON CONFLICT(id) DO UPDATE SET data = excluded.data
            "#,
        )
        .bind(key)
        .bind(json_data)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn get<T>(&self, key: &str) -> Result<Option<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync,
    {
        let result = sqlx::query(
            r#"
            SELECT data FROM conversation_history
            WHERE id = ?
            "#,
        )
        .bind(key)
        .fetch_optional(&self.pool)
        .await?;

        match result {
            Some(row) => {
                let data: String = row.get(0);
                Ok(Some(serde_json::from_str(&data)?))
            }
            None => Ok(None),
        }
    }

    async fn list<T>(&self) -> Result<Vec<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync,
    {
        let rows = sqlx::query(
            r#"
            SELECT data FROM conversation_history
            "#,
        )
        .fetch_all(&self.pool)
        .await?;

        let mut items = Vec::with_capacity(rows.len());
        for row in rows {
            let data: String = row.get(0);
            items.push(serde_json::from_str(&data)?);
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use tempfile::NamedTempFile;
    use uuid::Uuid;

    use super::*;

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct TestItem {
        name: String,
        value: i32,
    }

    async fn create_test_storage() -> (SqliteStorage, NamedTempFile) {
        let file = NamedTempFile::new().unwrap();
        let storage = SqliteStorage::new(file.path()).await.unwrap();
        (storage, file)
    }

    #[tokio::test]
    async fn test_store_and_get() {
        let (storage, _file) = create_test_storage().await;

        let item = TestItem { name: "test".to_string(), value: 42 };
        let key = "1";
        storage.save(key, &item).await.unwrap();
        // Retrieve and verify
        let retrieved = storage.get(key).await.unwrap().unwrap();
        assert_eq!(item, retrieved);
    }

    #[tokio::test]
    async fn test_get_nonexistent() {
        let (storage, _file) = create_test_storage().await;

        // Generate a random UUID that won't exist in the database
        let nonexistent_id = Uuid::new_v4().to_string();
        let result = storage.get::<String>(&nonexistent_id).await.unwrap();
        assert!(result.is_none());
    }

    #[tokio::test]
    async fn test_list_empty() {
        let (storage, _file) = create_test_storage().await;

        let items = storage.list::<TestItem>().await.unwrap();
        assert!(items.is_empty());
    }

    #[tokio::test]
    async fn test_list_multiple_items() {
        let (storage, _file) = create_test_storage().await;

        let items = vec![
            TestItem { name: "first".to_string(), value: 1 },
            TestItem { name: "second".to_string(), value: 2 },
        ];

        // Store items and collect their UUIDs
        let mut ids = Vec::new();
        for item in &items {
            let id = uuid::Uuid::new_v4().to_string();
            storage.save(&id, item).await.unwrap();
            ids.push(id);
        }

        // Verify each ID is a valid UUID
        for id in &ids {
            assert!(Uuid::parse_str(id).is_ok());
        }

        // Retrieve and verify all items
        let retrieved = storage.list::<TestItem>().await.unwrap();
        assert_eq!(retrieved.len(), items.len());

        // Verify each item can be retrieved by its ID
        for (id, expected) in ids.iter().zip(items.iter()) {
            let item = storage.get::<TestItem>(id).await.unwrap().unwrap();
            assert_eq!(&item, expected);
        }
    }

    #[tokio::test]
    async fn test_concurrent_access() {
        let (storage, _file) = create_test_storage().await;
        let storage = std::sync::Arc::new(storage);

        let mut handles = vec![];

        // Spawn multiple tasks to store items concurrently
        for i in 0..10 {
            let storage = storage.clone();
            let handle = tokio::spawn(async move {
                let item = TestItem { name: format!("item_{}", i), value: i };
                let id = uuid::Uuid::new_v4().to_string();
                storage.save(&id, &item).await.unwrap();
                id
            });
            handles.push(handle);
        }

        // Wait for all tasks to complete and collect UUIDs
        let mut ids = vec![];
        for handle in handles {
            let id = handle.await.unwrap();
            assert!(Uuid::parse_str(&id).is_ok()); // Verify each ID is a valid UUID
            ids.push(id);
        }

        // Verify all items were stored
        let items = storage.list::<TestItem>().await.unwrap();
        assert_eq!(items.len(), 10);

        // Verify each ID exists
        for id in ids {
            assert!(storage.get::<TestItem>(&id).await.unwrap().is_some());
        }
    }
}
