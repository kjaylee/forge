//! Permission system for managing file system access.

mod config;
mod config_loader;
mod error;
mod service;
mod state;
mod types;

pub use config::{DirectoryConfig, GlobalConfig, PermissionConfig, ToolPermissionConfig};
pub use config_loader::{ConfigLoader, FORGE_PERMISSION_CONFIG};
pub use error::{PermissionError, PermissionResult};
pub use service::{PermissionService, TestPermissionService};
pub use state::PermissionState;
pub use types::Permission;