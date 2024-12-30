use async_trait::async_trait;
use serde::de::DeserializeOwned;
use serde::Serialize;

mod sqlite;

pub use sqlite::SqliteStorage;

#[async_trait]
pub trait Storage<T>: Send + Sync + std::fmt::Debug
where
    T: Serialize + DeserializeOwned + Send + Sync,
{
    /// Initialize the storage
    async fn init(&self) -> Result<(), StorageError>;

    /// Store an item and return its UUID
    async fn save(&self, key: &str, item: &T) -> Result<(), StorageError>;

    /// Retrieve an item by its UUID
    async fn get(&self, key: &str) -> Result<Option<T>, StorageError>;

    /// List all items
    async fn list(&self) -> Result<Vec<T>, StorageError>;
}

#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}
