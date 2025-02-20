mod anthropic;
mod open_router;

use anthropic::Anthropic;
use derive_setters::Setters;
use forge_domain::{Provider, ProviderService};
use open_router::{OpenRouter, Provider as OpenRouterProvider};

#[derive(Debug, Clone, Setters, Default)]
#[setters(strip_option)]
pub struct ProviderBuilder {
    provider: Option<Provider>,
}

impl ProviderBuilder {
    pub fn build(self) -> Result<Box<dyn ProviderService>, anyhow::Error> {
        let provider = self
            .provider
            .ok_or(anyhow::anyhow!("provider is required."))?;
        match provider {
            Provider::OpenRouter(api_key) => Ok(Box::new(
                OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenRouter)
                    .api_key(api_key)
                    .build()?,
            )),
            Provider::OpenAI(api_key) => Ok(Box::new(
                OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenAI)
                    .api_key(api_key)
                    .build()?,
            )),
            Provider::Anthropic(api_key) => {
                Ok(Box::new(Anthropic::builder().api_key(api_key).build()?))
            }
        }
    }
}
