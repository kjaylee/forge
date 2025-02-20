use std::fmt::Display;

use serde::{Deserialize, Serialize};

/// Providers that can be used.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Provider {
    OpenRouter,
    OpenAI,
    Anthropic,
}

impl Display for Provider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Provider::OpenRouter => write!(f, "OpenRouter"),
            Provider::OpenAI => write!(f, "OpenAI"),
            Provider::Anthropic => write!(f, "Anthropic"),
        }
    }
}

impl Provider {
    /// detects the active provider from base URL
    pub fn detect(url: &str) -> Option<Self> {
        match url {
            "https://api.openai.com/v1/" => Some(Self::OpenAI),
            "https://api.openrouter.io/v1/" => Some(Self::OpenRouter),
            "https://api.anthropic.com/v1/" => Some(Self::Anthropic),
            _ => None,
        }
    }
}
