use std::fmt::Display;

use derive_more::derive::From;
use serde::{Deserialize, Serialize};
use url::Url;

/// Providers that can be used.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, From)]
pub enum Provider {
    OpenAI { url: Url },
    Anthropic,
}

impl Provider {
    pub fn from_url(url: Url) -> Self {
        if url.as_str().starts_with(Self::ANTHROPIC_URL) {
            Provider::Anthropic
        } else {
            Provider::OpenAI { url }
        }
    }

    pub fn antinomy() -> Provider {
        Provider::OpenAI { url: Url::parse(Provider::ANTINOMY_URL).unwrap() }
    }

    pub fn openai() -> Provider {
        Provider::OpenAI { url: Url::parse(Provider::OPENAI_URL).unwrap() }
    }

    pub fn open_router() -> Provider {
        Provider::OpenAI { url: Url::parse(Provider::OPEN_ROUTER_URL).unwrap() }
    }

    pub fn anthropic() -> Provider {
        Provider::Anthropic
    }
}

impl Display for Provider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Provider::OpenAI { url } => write!(f, "OpenAI Compat {}", url),
            Provider::Anthropic => write!(f, "Anthropic"),
        }
    }
}

impl Provider {
    pub const OPEN_ROUTER_URL: &str = "https://openrouter.ai/api/v1/";
    pub const OPENAI_URL: &str = "https://api.openai.com/v1/";
    pub const ANTHROPIC_URL: &str = "https://api.anthropic.com/v1/";
    pub const ANTINOMY_URL: &str = "https://antinomy.ai/api/v1/";

    /// Converts the provider to it's base URL
    pub fn to_base_url(&self) -> Url {
        match self {
            Provider::OpenAI { url } => url.clone(),
            Provider::Anthropic => Url::parse(Self::ANTHROPIC_URL).unwrap(),
        }
    }

    pub fn is_open_router(&self) -> bool {
        match self {
            Provider::OpenAI { url } => url.as_str().starts_with(Self::OPEN_ROUTER_URL),
            Provider::Anthropic => false,
        }
    }

    pub fn is_open_ai(&self) -> bool {
        match self {
            Provider::OpenAI { url } => url.as_str().starts_with(Self::OPENAI_URL),
            Provider::Anthropic => false,
        }
    }
}
