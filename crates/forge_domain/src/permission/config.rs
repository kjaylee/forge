//! Configuration types for the permission system.

use std::collections::HashMap;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};

use super::PermissionState;
use crate::tool_name::ToolName;

/// Configuration for directory-specific permissions.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DirectoryConfig {
    /// The directory path this configuration applies to
    pub path: PathBuf,
    /// Maximum depth for directory traversal
    #[serde(default)]
    pub max_depth: Option<usize>,
    /// Whether to respect gitignore files
    #[serde(default = "default_true")]
    pub respect_gitignore: bool,
    /// Whether to include hidden files
    #[serde(default)]
    pub include_hidden: bool,
}

/// Configuration for a tool's permissions.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolPermissionConfig {
    /// Default permission state for this tool
    pub default_state: PermissionState,
    /// Directory-specific configurations
    #[serde(default)]
    pub directories: Vec<DirectoryConfig>,
    /// Whether to require explicit approval for paths outside CWD
    #[serde(default = "default_true")]
    pub require_approval_outside_cwd: bool,
}

impl Default for ToolPermissionConfig {
    fn default() -> Self {
        Self {
            default_state: PermissionState::Deny,
            directories: Vec::new(),
            require_approval_outside_cwd: true,
        }
    }
}

/// Root configuration type for the permission system.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PermissionConfig {
    /// Global permission settings
    #[serde(default)]
    pub global: GlobalConfig,
    /// Tool-specific permission configurations
    #[serde(default)]
    pub tools: HashMap<ToolName, ToolPermissionConfig>,
}

impl Default for PermissionConfig {
    fn default() -> Self {
        Self {
            global: GlobalConfig::default(),
            tools: HashMap::new(),
        }
    }
}

/// Global permission configuration settings.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GlobalConfig {
    /// Whether to use strict mode (deny by default)
    #[serde(default = "default_true")]
    pub strict_mode: bool,
    /// Maximum allowed directory depth
    #[serde(default = "default_max_depth")]
    pub max_depth: usize,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            strict_mode: true,
            max_depth: default_max_depth(),
        }
    }
}

/// Helper function for default bool value of true
const fn default_true() -> bool {
    true
}

/// Default maximum directory depth
const fn default_max_depth() -> usize {
    10
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permission::PermissionResult;

    #[test]
    fn test_serialize_config() {
        let config = PermissionConfig {
            global: GlobalConfig {
                strict_mode: true,
                max_depth: 5,
            },
            tools: {
                let mut map = HashMap::new();
                map.insert(
                    ToolName::new("fs_read"),
                    ToolPermissionConfig {
                        default_state: PermissionState::Deny,
                        directories: vec![DirectoryConfig {
                            path: PathBuf::from("/test/path"),
                            max_depth: Some(2),
                            respect_gitignore: true,
                            include_hidden: false,
                        }],
                        require_approval_outside_cwd: true,
                    },
                );
                map
            },
        };

        let serialized = serde_json::to_string_pretty(&config).unwrap();
        let deserialized: PermissionConfig = serde_json::from_str(&serialized).unwrap();
        assert!(deserialized.global.strict_mode);
        assert_eq!(deserialized.global.max_depth, 5);
    }

    #[test]
    fn test_default_global_config() {
        let config = GlobalConfig::default();
        assert!(config.strict_mode);
        assert_eq!(config.max_depth, 10);
    }

    #[test]
    fn test_yaml_config() {
        let yaml = r#"
global:
  strictMode: true
  maxDepth: 5
tools:
  fs_read:
    defaultState: Deny
    directories:
      - path: /test/path
        maxDepth: 2
        respectGitignore: true
        includeHidden: false
    requireApprovalOutsideCwd: true
"#;
        let config: PermissionConfig = serde_yaml::from_str(yaml).unwrap();
        assert_eq!(config.global.max_depth, 5);
        let tool_name = ToolName::new("fs_read");
        let fs_read = config.tools.get(&tool_name).unwrap();
        assert_eq!(fs_read.default_state, PermissionState::Deny);
    }

    #[test]
    fn test_basic_config() -> PermissionResult<()> {
        let mut tools = HashMap::new();
        tools.insert(
            ToolName::new("fs_read"),
            ToolPermissionConfig {
                default_state: PermissionState::Deny,
                directories: vec![],
                require_approval_outside_cwd: true,
            }
        );

        let config = PermissionConfig {
            global: GlobalConfig::default(),
            tools,
        };
        
        assert_eq!(config.global.max_depth, 10);
        assert!(config.global.strict_mode);
        Ok(())
    }

    #[test]
    fn test_tool_config() -> PermissionResult<()> {
        let mut tools = HashMap::new();
        tools.insert(
            ToolName::new("fs_read"),
            ToolPermissionConfig {
                default_state: PermissionState::Deny,
                directories: vec![],
                require_approval_outside_cwd: true,
            }
        );

        let config = PermissionConfig {
            global: GlobalConfig::default(),
            tools,
        };
        
        let tool_name = ToolName::new("fs_read");
        let fs_read = config.tools.get(&tool_name).unwrap();
        assert_eq!(fs_read.default_state, PermissionState::Deny);
        assert!(fs_read.require_approval_outside_cwd);
        Ok(())
    }

    #[test]
    fn test_path_validation() -> PermissionResult<()> {
        let mut tools = HashMap::new();
        tools.insert(
            ToolName::new("fs_read"),
            ToolPermissionConfig {
                default_state: PermissionState::Deny,
                directories: vec![],
                require_approval_outside_cwd: true,
            }
        );

        let config = PermissionConfig {
            global: GlobalConfig::default(),
            tools,
        };
        
        let tool_name = ToolName::new("fs_read");
        let fs_read = config.tools.get(&tool_name).unwrap();
        assert!(fs_read.directories.is_empty());
        Ok(())
    }
}