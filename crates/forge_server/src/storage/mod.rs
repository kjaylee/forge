use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};

mod sqlite;

pub use sqlite::SqliteStorage;

#[async_trait]
pub trait Storage<T>: Send + Sync
where
    T: Serialize + DeserializeOwned + Send + Sync,
{
    /// Initialize the storage
    async fn init(&self) -> Result<(), StorageError>;

    /// Store an item and return its UUID
    async fn set(&self, key: String, item: &T) -> Result<String, StorageError>;

    /// Retrieve an item by its UUID
    async fn get(&self, id: String) -> Result<Option<T>, StorageError>;

    /// List all items
    async fn list(&self) -> Result<Vec<T>, StorageError>;
}

#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
}
