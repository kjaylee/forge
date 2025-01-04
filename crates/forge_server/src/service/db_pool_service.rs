use diesel::r2d2::{ConnectionManager, Pool};
use diesel::sqlite::SqliteConnection;
use diesel_migrations::{EmbeddedMigrations, MigrationHarness};
use diesel::prelude::*;

use crate::Result;

pub type DbPool = Pool<ConnectionManager<SqliteConnection>>;

#[async_trait::async_trait]
pub trait DbPoolService: Send + Sync {
    async fn get_pool(&self) -> Result<DbPool>;
}

pub struct LiveDbPool {
    pool: DbPool,
}

impl LiveDbPool {
    pub fn new(cwd: &str, migrations: EmbeddedMigrations) -> Result<Self> {
        let db_path = format!("{}/conversations.db", cwd);

            // Run migrations first
            let mut conn = SqliteConnection::establish(&db_path)
                .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        conn.run_pending_migrations(migrations)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        drop(conn);

        // Create connection pool
        let manager = ConnectionManager::<SqliteConnection>::new(db_path);
        let pool = Pool::builder()
            .build(manager)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        Ok(Self { pool })
    }
}

#[async_trait::async_trait]
impl DbPoolService for LiveDbPool {
    async fn get_pool(&self) -> Result<DbPool> {
        Ok(self.pool.clone())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use tempfile::TempDir;

    pub struct TestDbPool {
        pool: DbPool,
        _temp_dir: TempDir, // Keep TempDir alive for the duration of TestDbPool
    }

    impl TestDbPool {
        pub fn new(migrations: EmbeddedMigrations) -> Result<Self> {
            let temp_dir = TempDir::new().unwrap();
            let db_path = temp_dir.path().join("test.db").to_str().unwrap().to_string();

            // Run migrations
            let mut conn = SqliteConnection::establish(&db_path)
                .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
            conn.run_pending_migrations(migrations)
                .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
            drop(conn);

            // Create connection pool
            let manager = ConnectionManager::<SqliteConnection>::new(db_path);
            let pool = Pool::builder()
                .build(manager)
                .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

            Ok(Self { 
                pool,
                _temp_dir: temp_dir 
            })
        }
    }

    #[async_trait::async_trait]
    impl DbPoolService for TestDbPool {
        async fn get_pool(&self) -> Result<DbPool> {
            Ok(self.pool.clone())
        }
    }
}
