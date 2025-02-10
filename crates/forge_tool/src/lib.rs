mod approve;
mod ask;
mod fetch;
mod fs;
mod learning;
mod outline;
mod patch;
mod select;
mod shell;
mod syn;
mod think;
mod utils;

use std::sync::Arc;

use fetch::Fetch;
use forge_domain::{EmbeddingsRepository, Environment, Tool};
use fs::*;
use learning::Learning;
use outline::Outline;
use patch::*;
use shell::Shell;
use think::Think;

pub fn tools(env: &Environment, learning_repo: Arc<dyn EmbeddingsRepository>) -> Vec<Tool> {
    vec![
        // Approve.into(),
        FSRead.into(),
        FSWrite.into(),
        FSRemove.into(),
        FSList::default().into(),
        FSSearch.into(),
        FSFileInfo.into(),
        // TODO: once ApplyPatchJson is stable we can delete ApplyPatch
        ApplyPatch.into(),
        // ApplyPatchJson.into(),
        Outline.into(),
        // SelectTool.into(),
        Shell::new(env.clone()).into(),
        Think::default().into(),
        Fetch::default().into(),
        Learning::new(learning_repo).into(),
    ]
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    // Mock embedding repository
    struct TestEmbeddingRepo;
    #[async_trait::async_trait]
    impl EmbeddingsRepository for TestEmbeddingRepo {
        async fn get(&self, _: Uuid) -> anyhow::Result<Option<Information>> {
            Ok(None)
        }

        async fn insert(&self, _: String, _: Vec<String>) -> anyhow::Result<Embedding> {
            Ok(Embedding::new(vec![]))
        }
        async fn search(
            &self,
            _: Embedding,
            _: Vec<String>,
            _: usize,
        ) -> anyhow::Result<Vec<Information>> {
            Ok(vec![])
        }
    }

    use forge_domain::{Embedding, Information};
    use uuid::Uuid;

    use super::*;

    /// Create a default test environment
    fn test_env() -> Environment {
        Environment {
            os: std::env::consts::OS.to_string(),
            cwd: std::env::current_dir().unwrap_or_default(),
            home: Some("/".into()),
            shell: if cfg!(windows) {
                "cmd.exe".to_string()
            } else {
                "/bin/sh".to_string()
            },
            api_key: String::new(),
            large_model_id: String::new(),
            small_model_id: String::new(),
            base_path: PathBuf::new(),
        }
    }

    #[test]
    fn test_tool_description_length() {
        const MAX_DESCRIPTION_LENGTH: usize = 1024;

        println!("\nTool description lengths:");

        let mut any_exceeded = false;
        let env = test_env();
        for tool in tools(&env, Arc::new(TestEmbeddingRepo)) {
            let desc_len = tool.definition.description.len();
            println!(
                "{:?}: {} chars {}",
                tool.definition.name,
                desc_len,
                if desc_len > MAX_DESCRIPTION_LENGTH {
                    "(!)"
                } else {
                    ""
                }
            );

            if desc_len > MAX_DESCRIPTION_LENGTH {
                any_exceeded = true;
            }
        }

        assert!(
            !any_exceeded,
            "One or more tools exceed the maximum description length of {}",
            MAX_DESCRIPTION_LENGTH
        );
    }
}
