mod anthropic;
mod open_router;

use anthropic::Anthropic;
use forge_domain::{Provider, ProviderService};
use open_router::{OpenRouter, Provider as OpenRouterProvider};

/// Creates an appropriate provider service based on the provider type.
pub struct ProviderFactory;

impl ProviderFactory {
    pub fn get(provider: Provider) -> Result<Box<dyn ProviderService>, anyhow::Error> {
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
