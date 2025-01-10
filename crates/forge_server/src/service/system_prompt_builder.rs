use std::sync::Arc;

use forge_domain::{Environment, ToolService};
use forge_provider::ProviderService;

use super::{system_prompt_service::SystemPromptService, Service};

pub struct SystemPrompt {
    env: Environment,
    tool: Arc<dyn ToolService>,
    provider: Arc<dyn ProviderService>,
    template: String,
}

impl SystemPrompt {
    pub fn new(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
    ) -> Self {
        Self { env, tool, provider, template: "".to_string() }
    }

    pub fn template(self, template: &str) -> SystemPrompt {
        SystemPrompt {
            env: self.env,
            tool: self.tool,
            provider: self.provider,
            template: template.to_string(),
        }
    }

    pub fn build(self) -> impl SystemPromptService {
        Service::system_prompt(self.env, self.tool, self.provider, self.template)
    }
}
