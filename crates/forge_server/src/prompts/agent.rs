use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, Default)]
pub enum Agent {
    #[default]
    Coding,
    TitleGenerator,
}

#[derive(Debug, Clone)]
pub struct PromptPath {
    pub(crate) system: PathBuf,
    pub(crate) user: PathBuf,
}

impl PromptPath {
    pub fn user(&self) -> String {
        self.user.to_string_lossy().to_string()
    }

    pub fn system(&self) -> String {
        self.system.to_string_lossy().to_string()
    }
}

impl Agent {
    fn prompt_dir(self) -> &'static str {
        match self {
            Agent::Coding => "coding",
            Agent::TitleGenerator => "title",
        }
    }

    pub fn prompt_path(self) -> PromptPath {
        // Using absolute paths for prompt files
        let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let prompts_dir = crate_root.join("src").join("prompts");

        PromptPath {
            system: prompts_dir.join(self.prompt_dir()).join("system.md"),
            user: prompts_dir.join(self.prompt_dir()).join("user_task.md"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl PromptPath {
        pub fn exists(&self) -> bool {
            self.system.exists() && self.user.exists()
        }

        pub fn system_exists(&self) -> bool {
            self.system.exists()
        }

        pub fn user_exists(&self) -> bool {
            self.user.exists()
        }
    }

    #[test]
    fn test_prompt_paths_exist() {
        let paths = Agent::Coding.prompt_path();
        assert!(paths.system.exists(), "System prompt file should exist");
        assert!(paths.user.exists(), "User prompt file should exist");
    }

    #[test]
    fn test_individual_paths_exist() {
        let paths = Agent::Coding.prompt_path();
        assert!(paths.system_exists(), "System prompt should exist");
        assert!(paths.user_exists(), "User prompt should exist");
    }
}
