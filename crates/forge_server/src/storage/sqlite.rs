#![allow(dead_code)]
use super::{Storage, StorageError};
use serde::{de::DeserializeOwned, Serialize};
use sqlx::{Row, SqlitePool};
use std::marker::PhantomData;
use std::path::Path;

pub struct SqliteStorage<T> {
    pool: SqlitePool,
    _phantom: PhantomData<T>,
}

impl<T> SqliteStorage<T>
where
    T: Serialize + DeserializeOwned + Send + Sync,
{
    pub async fn new(db_path: impl AsRef<Path>) -> Result<Self, StorageError> {
        let db_url = format!("sqlite://{}", db_path.as_ref().to_string_lossy());
        let pool = SqlitePool::connect(&db_url).await?;

        let storage = Self { pool, _phantom: PhantomData };
        storage.init().await?;
        Ok(storage)
    }
}

#[async_trait::async_trait]
impl<T> Storage<T> for SqliteStorage<T>
where
    T: Serialize + DeserializeOwned + Send + Sync,
{
    async fn init(&self) -> Result<(), StorageError> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS items (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                data TEXT NOT NULL,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
            "#,
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    async fn set(&self, item: &T) -> Result<i64, StorageError> {
        let json_data = serde_json::to_string(item)?;

        let result = sqlx::query(
            r#"
            INSERT INTO items (data)
            VALUES (?)
            RETURNING id
            "#,
        )
        .bind(json_data)
        .fetch_one(&self.pool)
        .await?;

        Ok(result.get::<i64, _>("id"))
    }

    async fn get(&self, id: i64) -> Result<Option<T>, StorageError> {
        let record = sqlx::query(
            r#"
            SELECT data
            FROM items
            WHERE id = ?
            "#,
        )
        .bind(id)
        .fetch_optional(&self.pool)
        .await?;

        match record {
            Some(row) => {
                let data: String = row.get("data");
                let item = serde_json::from_str(&data)?;
                Ok(Some(item))
            }
            None => Ok(None),
        }
    }

    async fn list(&self) -> Result<Vec<T>, StorageError> {
        let records = sqlx::query(
            r#"
            SELECT data
            FROM items
            "#,
        )
        .fetch_all(&self.pool)
        .await?;

        let mut items = Vec::with_capacity(records.len());
        for row in records {
            let data: String = row.get("data");
            let item = serde_json::from_str(&data)?;
            items.push(item);
        }

        Ok(items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};
    use tempfile::NamedTempFile;

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct TestItem {
        name: String,
        value: i32,
    }

    async fn create_test_storage() -> (SqliteStorage<TestItem>, NamedTempFile) {
        let file = NamedTempFile::new().unwrap();
        let storage = SqliteStorage::new(file.path()).await.unwrap();
        (storage, file)
    }

    #[tokio::test]
    async fn test_store_and_get() {
        let (storage, _file) = create_test_storage().await;

        let item = TestItem { name: "test".to_string(), value: 42 };

        // Store the item
        let id = storage.set(&item).await.unwrap();

        // Retrieve and verify
        let retrieved = storage.get(id).await.unwrap().unwrap();
        assert_eq!(item, retrieved);
    }

    #[tokio::test]
    async fn test_get_nonexistent() {
        let (storage, _file) = create_test_storage().await;

        let result = storage.get(1).await.unwrap();
        assert!(result.is_none());
    }

    #[tokio::test]
    async fn test_list_empty() {
        let (storage, _file) = create_test_storage().await;

        let items = storage.list().await.unwrap();
        assert!(items.is_empty());
    }

    #[tokio::test]
    async fn test_list_multiple_items() {
        let (storage, _file) = create_test_storage().await;

        let items = vec![
            TestItem { name: "first".to_string(), value: 1 },
            TestItem { name: "second".to_string(), value: 2 },
        ];

        // Store items
        for item in &items {
            storage.set(item).await.unwrap();
        }

        // Retrieve and verify
        let retrieved = storage.list().await.unwrap();
        assert_eq!(retrieved.len(), items.len());

        // Items should be returned in reverse order (newest first)
        assert_eq!(retrieved[0], items[0]);
        assert_eq!(retrieved[1], items[1]);
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
                storage.set(&item).await.unwrap()
            });
            handles.push(handle);
        }

        // Wait for all tasks to complete
        let mut ids = vec![];
        for handle in handles {
            ids.push(handle.await.unwrap());
        }

        // Verify all items were stored
        let items = storage.list().await.unwrap();
        assert_eq!(items.len(), 10);

        // Verify each ID exists
        for id in ids {
            assert!(storage.get(id).await.unwrap().is_some());
        }
    }
}
