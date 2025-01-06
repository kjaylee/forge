use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, Default)]
pub enum Agents {
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
    pub fn exists(&self) -> bool {
        self.system.exists() && self.user.exists()
    }

    pub fn user(&self) -> String {
        self.user.to_string_lossy().to_string()
    }

    pub fn system(&self) -> String {
        self.system.to_string_lossy().to_string()
    }

    pub fn system_exists(&self) -> bool {
        self.system.exists()
    }

    pub fn user_exists(&self) -> bool {
        self.user.exists()
    }
}

impl Agents {
    fn dir_name(self) -> &'static str {
        match self {
            Agents::Coding => "coding",
            Agents::TitleGenerator => "title",
        }
    }

    pub fn prompt_path(self) -> PromptPath {
        let prompts_dir = Path::new("src").join("prompts");
        let agent_dir = prompts_dir.join(self.dir_name());

        PromptPath {
            system: agent_dir.join("system.md"),
            user: agent_dir.join("user_task.md"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prompt_paths_exist() {
        let paths = Agents::Coding.prompt_path();
        println!("{:?}", paths);
        assert!(paths.exists(), "Prompt files should exist");
    }

    #[test]
    fn test_individual_paths_exist() {
        let paths = Agents::Coding.prompt_path();
        assert!(paths.system_exists(), "System prompt should exist");
        assert!(paths.user_exists(), "User prompt should exist");
    }
}
