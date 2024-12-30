use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};

mod sqlite;

#[async_trait]
pub trait Storage<T>: Send + Sync
where
    T: Serialize + DeserializeOwned + Send + Sync,
{
    /// Initialize the storage
    async fn init(&self) -> Result<(), StorageError>;

    /// Store an item and return its ID
    async fn set(&self, item: &T) -> Result<i64, StorageError>;

    /// Retrieve an item by its ID
    async fn get(&self, id: i64) -> Result<Option<T>, StorageError>;

    /// List all stored items
    async fn list(&self) -> Result<Vec<T>, StorageError>;
}

#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
}
