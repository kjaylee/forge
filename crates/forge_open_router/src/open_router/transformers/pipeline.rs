use super::drop_tool_call::DropToolCalls;
use super::identity::Identity;
use super::open_ai::OpenAITransformer;
use super::set_cache::SetCache;
use super::tool_choice::SetToolChoice;
use super::Transformer;
use crate::open_router::provider::Provider;
use crate::open_router::request::OpenRouterRequest;
use crate::open_router::tool_choice::ToolChoice;

/// Pipeline for transforming requests based on the provider type
pub struct ProviderPipeline<'a>(&'a Provider);

impl<'a> ProviderPipeline<'a> {
    /// Creates a new provider pipeline for the given provider
    pub fn new(provider: &'a Provider) -> Self {
        Self(provider)
    }
}

impl Transformer for ProviderPipeline<'_> {
    fn transform(&self, request: OpenRouterRequest) -> OpenRouterRequest {
        let or_transformers = Identity
            .combine(DropToolCalls.when_name(|name| name.contains("mistral")))
            .combine(SetToolChoice::new(ToolChoice::Auto).when_name(|name| name.contains("gemini")))
            .combine(SetCache.when_name(|name| {
                ["mistral", "gemini", "openai"]
                    .iter()
                    .all(|p| !name.contains(p))
            }))
            .when(move |_| self.0.is_open_router());

        let openai_transformers = OpenAITransformer.when(move |_| self.0.is_openai());

        or_transformers
            .combine(openai_transformers)
            .transform(request)
    }
}
