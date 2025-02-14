use std::time::Duration;

use derive_setters::Setters;
use diesel::r2d2::{ConnectionManager, Pool};
use diesel::SqliteConnection;
use forge_domain::Environment;
use tokio::sync::Mutex;
use tokio_retry::strategy::ExponentialBackoff;
use tokio_retry::Retry;

type SQLConnection = Pool<ConnectionManager<SqliteConnection>>;

#[derive(Debug, Setters)]
pub struct ForgeConnection {
    #[setters(skip)]
    env: Environment,
    #[setters(skip)]
    conn: Mutex<Option<SQLConnection>>,
    busy_timeout: Duration,
    max_connections: u32,
    connection_timeout: Duration,
    attempts: usize,
}

impl ForgeConnection {
    pub fn new(env: Environment) -> Self {
        Self {
            env,
            conn: Mutex::new(None),
            busy_timeout: Duration::from_secs(30),
            max_connections: 5,
            connection_timeout: Duration::from_secs(30),
            attempts: 10,
        }
    }

    pub async fn init(&self) -> anyhow::Result<SQLConnection> {
        let retry_strategy = ExponentialBackoff::from_millis(100)
            .factor(2)
            .take(self.attempts);

        Retry::spawn(retry_strategy, || self.init_once()).await
    }

    async fn init_once(&self) -> anyhow::Result<SQLConnection> {
        let mut guard = self.conn.lock().await;
        if let Some(conn) = guard.as_ref() {
            Ok(conn.clone())
        } else {
            let db_path = self.env.db_path().display().to_string();
            let manager = ConnectionManager::new(db_path);
            let pool = Pool::builder()
                .max_size(self.max_connections)
                .connection_timeout(self.connection_timeout)
                .test_on_check_out(true)
                .build(manager)?;

            *guard = Some(pool.clone());
            Ok(pool)
        }
    }
}
