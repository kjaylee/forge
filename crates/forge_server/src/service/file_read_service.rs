use super::Service;
use crate::Result;

#[async_trait::async_trait]
pub trait FileReadService: Send + Sync {
    async fn read(&self, path: String) -> Result<String>;
}

impl Service {
    pub fn file_read_service() -> impl FileReadService {
        Live {}
    }
}

struct Live;

#[async_trait::async_trait]
impl FileReadService for Live {
    async fn read(&self, path: String) -> Result<String> {
        Ok(tokio::fs::read_to_string(path).await?)
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::prompts::Agent;

    pub struct TestFileReadService(HashMap<String, String>);

    impl TestFileReadService {
        pub fn default() -> Self {
            let mut map = HashMap::new();

            let mut load_templates = |agent: &Agent| {
                let prompts = agent.prompt_path();
                let system_template = std::fs::read_to_string(&prompts.system).unwrap();
                let user_template = std::fs::read_to_string(&prompts.user).unwrap();

                map.insert(prompts.user(), user_template);
                map.insert(prompts.system(), system_template);
            };

            load_templates(&Agent::Coding);
            load_templates(&Agent::TitleGenerator);

            Self(map)
        }

        pub fn new(s: HashMap<String, String>) -> Self {
            let mut default_file_read = Self::default();
            default_file_read.0.extend(s);
            default_file_read
        }
    }

    #[async_trait::async_trait]
    impl FileReadService for TestFileReadService {
        async fn read(&self, path: String) -> Result<String> {
            self.0.get(&path).cloned().ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    format!("File not found: {}", path),
                )
                .into()
            })
        }
    }
}
