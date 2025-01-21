use anyhow::Result;
use r2d2::Pool;
use r2d2_sqlite::SqliteConnectionManager;
use rusqlite::{ffi::sqlite3_auto_extension, Connection};
use sqlite_vec::sqlite3_vec_init;
use tracing::debug;

use crate::sqlite::Sqlite;

use super::Service;

pub type SQLConnection = Pool<SqliteConnectionManager>;

const DB_NAME: &str = ".forge.db";

impl Service {
    pub fn rusqlite_pool_service(db_path: &str) -> Result<impl Sqlite<Pool = SQLConnection>> {
        Live::new(db_path)
    }
}

struct Live {
    pool: SQLConnection,
}

impl Live {
    fn new(db_path: &str) -> Result<Self> {
        // registers the custom extension function
        unsafe {
            sqlite3_auto_extension(Some(sqlite3_vec_init));
        }

        let db_path = format!("{}/{}", db_path, DB_NAME);

        // Initialize database and run any setup
        let conn = Connection::open(&db_path)?;

        // Here you would typically run your migrations
        // For now, we'll just ensure the database is created
        debug!("Database initialized: {}", db_path);

        drop(conn);

        // Create connection pool
        let manager = SqliteConnectionManager::file(db_path);
        let pool = Pool::builder()
            .max_size(10) // adjust based on your needs
            .build(manager)?;

        Ok(Live { pool })
    }
}

#[async_trait::async_trait]
impl Sqlite for Live {
    type Pool = SQLConnection;
    async fn pool(&self) -> Result<Self::Pool> {
        Ok(self.pool.clone())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use rusqlite::params;
    use tempfile::TempDir;

    pub struct TestSqlite {
        live: Live,
        _temp_dir: TempDir,
    }

    impl TestSqlite {
        pub fn new() -> Result<Self> {
            let temp_dir = TempDir::new().unwrap();
            let db_path = temp_dir.path().to_str().unwrap().to_string();

            Ok(Self { live: Live::new(&db_path)?, _temp_dir: temp_dir })
        }
    }

    #[async_trait::async_trait]
    impl Sqlite for TestSqlite {
        type Pool = SQLConnection;
        async fn pool(&self) -> Result<Self::Pool> {
            Ok(self.live.pool.clone())
        }
    }

    #[tokio::test]
    async fn test_create_and_connect() -> Result<()> {
        let db = TestSqlite::new()?;
        let pool = db.pool().await?;

        // Test that we can get a connection
        let conn = pool.get()?;
        assert!(conn.is_autocommit());
        Ok(())
    }

    #[tokio::test]
    async fn test_basic_operations() -> Result<()> {
        let db = TestSqlite::new()?;
        let pool = db.pool().await?;
        let conn = pool.get()?;

        // Create a test table
        conn.execute(
            "CREATE TABLE test (id INTEGER PRIMARY KEY, name TEXT NOT NULL)",
            [],
        )?;

        // Test insert
        conn.execute("INSERT INTO test (name) VALUES (?1)", params!["test_name"])?;

        // Test select
        let mut stmt = conn.prepare("SELECT name FROM test WHERE id = 1")?;
        let name: String = stmt.query_row([], |row| row.get(0))?;
        assert_eq!(name, "test_name");

        Ok(())
    }
}
