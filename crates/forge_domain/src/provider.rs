use serde::{Deserialize, Serialize};

/// Providers that can be used.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Provider {
    OpenRouter(String),
    OpenAI(String),
    Anthropic(String),
}

impl Provider {
    /// detects the active provider from the environment variables.
    pub fn detect() -> Option<Self> {
        let open_router_key = std::env::var("OPEN_ROUTER_KEY");
        let open_ai_key = std::env::var("OPEN_AI_KEY");
        let anthropic_key = std::env::var("ANTHROPIC_KEY");
        match (open_router_key, open_ai_key, anthropic_key) {
            (Ok(key), _, _) => Some(Self::OpenRouter(key)),
            (_, Ok(key), _) => Some(Self::OpenAI(key)),
            (_, _, Ok(key)) => Some(Self::Anthropic(key)),
            _ => None,
        }
    }
}
