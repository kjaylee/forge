use forge_domain::Provider;

use super::drop_tool_call::DropToolCalls;
use super::identity::Identity;
use super::make_openai_compat::MakeOpenAiCompat;
use super::set_cache::SetCache;
use super::tool_choice::SetToolChoice;
use super::Transformer;
use crate::forge_provider::request::Request;
use crate::forge_provider::tool_choice::ToolChoice;

/// Pipeline for transforming requests based on the provider type
pub struct ProviderPipeline<'a>(&'a Provider);

impl<'a> ProviderPipeline<'a> {
    /// Creates a new provider pipeline for the given provider
    pub fn new(provider: &'a Provider) -> Self {
        Self(provider)
    }
}

impl Transformer for ProviderPipeline<'_> {
    fn transform(&self, request: Request) -> Request {
        // Only Anthropic and Gemini requires cache configuration to be set.
        // ref: https://openrouter.ai/docs/features/prompt-caching
        let or_transformers = Identity
            .combine(DropToolCalls.when_model("mistral"))
            .combine(SetToolChoice::new(ToolChoice::Auto).when_model("gemini"))
            .combine(SetCache.when_model("gemini|anthropic"))
            .when(move |_| self.0.is_open_router() || self.0.is_antinomy());

        let open_ai_compat =
            MakeOpenAiCompat.when(move |_| !(self.0.is_antinomy() || self.0.is_open_router()));

        or_transformers.combine(open_ai_compat).transform(request)
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::ModelId;

    use crate::forge_provider::{
        request::{Message, MessageContent, Request, Role, Transform},
        transformers::{ProviderPipeline, Transformer},
    };

    impl Message {
        pub fn text_message(role: Role, content: &str) -> Self {
            Message {
                role,
                content: Some(MessageContent::Text(content.into())),
                name: None,
                tool_call_id: None,
                tool_calls: None,
            }
        }
    }

    fn messages() -> Vec<Message> {
        vec![
            Message::text_message(Role::System, "system-prompt"),
            Message::text_message(Role::User, "user-prompt-1"),
            Message::text_message(Role::Assistant, "assistant-prompt-1"),
            Message::text_message(Role::User, "user-prompt-2"),
            Message::text_message(Role::Assistant, "assistant-prompt-2"),
            Message::text_message(Role::User, "user-prompt-3"),
            Message::text_message(Role::Assistant, "assistant-prompt-3"),
        ]
    }

    #[test]
    fn should_set_cache_on_anthropic_models() {
        let request = Request::default()
            .model(ModelId::new("anthropic/sonnet-4"))
            .messages(messages());
        let provider = forge_domain::Provider::antinomy("abc");
        let request = ProviderPipeline::new(&provider).transform(request);
        assert!(request
            .messages
            .unwrap()
            .iter()
            .filter_map(|message| message.content.as_ref())
            .any(|message_content| message_content.is_cached()));
    }

    #[test]
    fn should_preserve_the_antinomy_parameters() {
        let request = Request::default()
            .model(ModelId::new("anthropic/sonnet-4"))
            .messages(messages())
            .transforms(vec![Transform::default()]);
        let provider = forge_domain::Provider::antinomy("abc");
        let transformed_request = ProviderPipeline::new(&provider).transform(request);
        assert_eq!(
            transformed_request.transforms,
            Some(vec![Transform::default()])
        );

        let request = Request::default()
            .model(ModelId::new("anthropic/sonnet-4"))
            .messages(messages())
            .transforms(vec![Transform::default()]);
        let provider = forge_domain::Provider::open_router("abc");
        let transformed_request = ProviderPipeline::new(&provider).transform(request);
        assert_eq!(
            transformed_request.transforms,
            Some(vec![Transform::default()])
        );
    }

    #[test]
    fn should_drop_unsupported_params_for_openai() {
        let request = Request::default()
            .model(ModelId::new("openai/codex-mini"))
            .messages(messages())
            .transforms(vec![Transform::default()]);
        let provider = forge_domain::Provider::openai("abc");
        let transformed_request = ProviderPipeline::new(&provider).transform(request);
        assert_eq!(transformed_request.transforms, None);
    }
}
