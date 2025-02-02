use std::path::PathBuf;

use async_trait::async_trait;
use derive_setters::Setters;
use serde::Serialize;

#[derive(Default, Serialize, Debug, Setters, Clone)]
#[serde(rename_all = "camelCase")]
#[setters(strip_option)]
/// Represents the environment in which the application is running.
pub struct Environment {
    /// The operating system of the environment.
    pub os: String,
    /// The current working directory.
    pub cwd: PathBuf,
    /// The home directory.
    pub home: Option<PathBuf>,
    /// The shell being used.
    pub shell: String,
    /// The Forge API key.
    pub api_key: String,
    /// The large model ID.
    pub large_model_id: String,
    /// The small model ID.
    pub small_model_id: String,

    /// The base path relative to which everything else stored.
    pub base_path: PathBuf,
}

impl Environment {
    pub fn db_path(&self) -> PathBuf {
        self.base_path.clone()
    }

    pub fn log_path(&self) -> PathBuf {
        self.base_path.join("logs")
    }

    pub fn history_path(&self) -> PathBuf {
        self.base_path.clone()
    }

    pub fn from_cwd(cwd: PathBuf) -> anyhow::Result<Environment> {
        dotenv::dotenv().ok();
        let api_key = std::env::var("OPEN_ROUTER_KEY").expect("OPEN_ROUTER_KEY must be set");
        let large_model_id =
            std::env::var("FORGE_LARGE_MODEL").unwrap_or("anthropic/claude-3.5-sonnet".to_owned());
        let small_model_id =
            std::env::var("FORGE_SMALL_MODEL").unwrap_or("anthropic/claude-3.5-haiku".to_owned());

        Ok(Environment {
            os: std::env::consts::OS.to_string(),
            cwd,
            shell: if cfg!(windows) {
                std::env::var("COMSPEC")?
            } else {
                std::env::var("SHELL").unwrap_or("/bin/sh".to_string())
            },
            api_key,
            large_model_id,
            small_model_id,
            base_path: base_path(),
            home: dirs::home_dir(),
        })
    }
}

fn base_path() -> PathBuf {
    dirs::config_dir()
        .map(|a| a.join("forge"))
        .unwrap_or(PathBuf::from(".").join(".forge"))
}

/// Repository for accessing system environment information
#[async_trait]
pub trait EnvironmentRepository {
    /// Get the current environment information including:
    /// - Operating system
    /// - Current working directory
    /// - Home directory
    /// - Default shell
    async fn get_environment(&self) -> anyhow::Result<Environment>;
}
