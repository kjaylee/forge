use forge_domain::ModelId;

use super::system_prompt_service::SystemPromptService;
use super::Service;
use crate::Result;

struct Live;

impl Service {
    pub fn title_system_prompt_service() -> impl SystemPromptService {
        Live {}
    }
}

#[async_trait::async_trait]
impl SystemPromptService for Live {
    async fn get_system_prompt(&self, _: &ModelId) -> Result<String> {
        let template = include_str!("../prompts/title/system.md");
        Ok(template.to_string())
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::ModelId;

    use super::*;

    #[tokio::test]
    async fn test_title_system_prompt_service() {
        let service = Service::title_system_prompt_service();
        let model_id = ModelId::default();
        let system_prompt = service.get_system_prompt(&model_id).await.unwrap();
        insta::assert_snapshot!(system_prompt);
    }
}
