use async_trait::async_trait;
use derive_more::derive::{Display, From};
use serde::de::DeserializeOwned;
use serde::Serialize;
use serde_json::Error;

mod sqlite;

pub use sqlite::SqliteStorage;

#[async_trait]
pub trait Storage: Send + Sync + std::fmt::Debug + Clone {
    /// Initialize the storage
    async fn init(&self) -> Result<(), StorageError>;

    /// Store an item and return its UUID
    async fn save<T>(&self, key: &str, item: &T) -> Result<(), StorageError>
    where
        T: Serialize + Send + Sync;

    /// Retrieve an item by its UUID
    async fn get<T>(&self, key: &str) -> Result<Option<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync;

    /// List all items
    async fn list<T>(&self) -> Result<Vec<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync;
}

#[derive(Debug, From, Display)]
pub enum StorageError {
    Database(#[from] sqlx::Error),
    Serialization(#[from] Error),
    Io(#[from] std::io::Error),
}
