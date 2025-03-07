use std::path::PathBuf;

use forge_app::EnvironmentService;
use forge_domain::{Environment, Provider};

pub struct ForgeEnvironmentService {
    restricted: bool,
}

impl ForgeEnvironmentService {
    /// Creates a new EnvironmentFactory with current working directory
    ///
    /// # Arguments
    /// * `unrestricted` - If true, use unrestricted shell mode (sh/bash) If
    ///   false, use restricted shell mode (rbash)
    pub fn new(restricted: bool) -> Self {
        Self { restricted }
    }

    /// Get path to appropriate shell based on platform and mode
    fn get_shell_path(&self) -> String {
        if cfg!(target_os = "windows") {
            std::env::var("COMSPEC").unwrap_or("cmd.exe".to_string())
        } else if self.restricted {
            // Default to rbash in restricted mode
            "/bin/rbash".to_string()
        } else {
            // Use user's preferred shell or fallback to sh
            std::env::var("SHELL").unwrap_or("/bin/sh".to_string())
        }
    }

    fn get(&self) -> Environment {
        dotenv::dotenv().ok();
        let cwd = std::env::current_dir().unwrap_or(PathBuf::from("."));
        let keys = [
            ("FORGE_KEY", Provider::antinomy()),
            ("OPENROUTER_API_KEY", Provider::open_router()),
            ("OPENAI_API_KEY", Provider::openai()),
            ("ANTHROPIC_API_KEY", Provider::anthropic()),
        ];

        let env_variables = keys
            .iter()
            .map(|(key, _)| *key)
            .collect::<Vec<_>>()
            .join(", ");

        let (provider_key, provider) = keys
            .iter()
            .find_map(|(key, url)| std::env::var(key).ok().map(|key| (key, url.clone())))
            .unwrap_or_else(|| panic!("No API key found. Please set one of: {}", env_variables));

        Environment {
            os: std::env::consts::OS.to_string(),
            pid: std::process::id(),
            cwd,
            shell: self.get_shell_path(),
            base_path: dirs::config_dir()
                .map(|a| a.join("forge"))
                .unwrap_or(PathBuf::from(".").join(".forge")),
            home: dirs::home_dir(),

            qdrant_key: std::env::var("QDRANT_KEY").ok(),
            qdrant_cluster: std::env::var("QDRANT_CLUSTER").ok(),
            provider_key,
            provider_url: provider.to_base_url().to_string(),
            openai_key: std::env::var("OPENAI_API_KEY").ok(),
        }
    }
}

impl EnvironmentService for ForgeEnvironmentService {
    fn get_environment(&self) -> Environment {
        self.get()
    }
}
