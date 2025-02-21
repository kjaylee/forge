use std::fmt::Display;

use serde::{Deserialize, Serialize};

// Base URLs for providers.
const OPEN_ROUTER_URL: &str = "https://openrouter.ai/api/v1/";
const OPENAI_URL: &str = "https://api.openai.com/v1/";
const ANTHROPIC_URL: &str = "https://api.anthropic.com/v1/";

// Environment variables for providers.
const OPEN_AI: &str = "OPEN_AI_KEY";
const OPEN_ROUTER: &str = "OPEN_ROUTER_KEY";
const ANTHROPIC: &str = "ANTHROPIC_KEY";
const FORGE: &str = "FORGE_KEY";
const FORGE_PROVIDER_URL: &str = "FORGE_PROVIDER_URL";

/// Providers that can be used.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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
    /// Maps environment variables to provider
    pub fn from_env() -> Option<Self> {
        match (
            std::env::var(FORGE),
            std::env::var(OPEN_ROUTER),
            std::env::var(OPEN_AI),
            std::env::var(ANTHROPIC),
        ) {
            (Ok(_), _, _, _) => {
                // note: if we're using FORGE_KEY, we need FORGE_PROVIDER_URL to be set.
                let provider_url = std::env::var(FORGE_PROVIDER_URL).ok()?;
                Self::from_url(&provider_url)
            }
            (_, Ok(_), _, _) => Some(Self::OpenRouter),
            (_, _, Ok(_), _) => Some(Self::OpenAI),
            (_, _, _, Ok(_)) => Some(Self::Anthropic),
            (Err(_), Err(_), Err(_), Err(_)) => None,
        }
    }

    /// Maps provider to it's base URL
    pub fn to_base_url(&self) -> &str {
        match self {
            Provider::OpenRouter => OPEN_ROUTER_URL,
            Provider::OpenAI => OPENAI_URL,
            Provider::Anthropic => ANTHROPIC_URL,
        }
    }

    /// Reads the key for provider from env.
    pub fn to_key(&self) -> Option<String> {
        // note: `forge` env can hold the key for all providers.
        match self {
            Provider::OpenRouter => std::env::var(OPEN_ROUTER).or(std::env::var(FORGE)),
            Provider::OpenAI => std::env::var(OPEN_AI).or(std::env::var(FORGE)),
            Provider::Anthropic => std::env::var(ANTHROPIC).or(std::env::var(FORGE)),
        }
        .ok()
    }

    /// Converts url to provider
    pub fn from_url(url: &str) -> Option<Self> {
        match url {
            OPENAI_URL => Some(Self::OpenAI),
            OPEN_ROUTER_URL => Some(Self::OpenRouter),
            ANTHROPIC_URL => Some(Self::Anthropic),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::env;

    use super::*;


    // To avoid flakyness with parallel runnings tests, use this helper function to set/remove env variables.
    fn with_env(env_var: &str, value: &str, fnn: fn()) {
        env::set_var(env_var, value);
        fnn();
        env::remove_var(env_var);
    }

    #[test]
    fn test_from_env() {
        // test: test_provider_from_env_with_forge_key_and_without_provider_url
        with_env(FORGE, "", || {
            let provider = Provider::from_env();
            assert_eq!(provider, None);
        });

        // test: test_provider_from_env_with_forge_key
        with_env(FORGE, "some_forge_key", || {
            with_env(FORGE_PROVIDER_URL, "https://api.openai.com/v1/", || {
                let provider = Provider::from_env();
                assert_eq!(provider, Some(Provider::OpenAI));
                assert_eq!(
                    provider.unwrap().to_key(),
                    Some("some_forge_key".to_string())
                );
            });
        });

        // test: test_provider_from_env_with_open_router_key
        with_env(OPEN_ROUTER, "some_open_router_key", || {
            let provider = Provider::from_env();
            assert_eq!(provider, Some(Provider::OpenRouter));
            assert_eq!(
                provider.unwrap().to_key(),
                Some("some_open_router_key".to_string())
            );
        });

        // test: test_provider_from_env_with_openai_key
        with_env(OPEN_AI, "some_openai_key", || {
            let provider = Provider::from_env();
            assert_eq!(provider, Some(Provider::OpenAI));
            assert_eq!(
                provider.unwrap().to_key(),
                Some("some_openai_key".to_string())
            );
        });

        // test: test_provider_from_env_with_anthropic_key
        with_env(ANTHROPIC, "some_anthropic_key", || {
            let provider = Provider::from_env();
            assert_eq!(provider, Some(Provider::Anthropic));
            assert_eq!(
                provider.unwrap().to_key(),
                Some("some_anthropic_key".to_string())
            );
        });

        // test: test_provider_from_env_with_no_keys
        with_env("test", "test", || {
            let provider = Provider::from_env();
            assert_eq!(provider, None);
        });
    }

    #[test]
    fn test_from_url() {
        assert_eq!(
            Provider::from_url("https://api.openai.com/v1/"),
            Some(Provider::OpenAI)
        );
        assert_eq!(
            Provider::from_url("https://openrouter.ai/api/v1/"),
            Some(Provider::OpenRouter)
        );
        assert_eq!(
            Provider::from_url("https://api.anthropic.com/v1/"),
            Some(Provider::Anthropic)
        );
        assert_eq!(Provider::from_url("https://unknown.url/"), None);
    }

    #[test]
    fn test_to_url() {
        assert_eq!(Provider::OpenAI.to_base_url(), OPENAI_URL);
        assert_eq!(Provider::OpenRouter.to_base_url(), OPEN_ROUTER_URL);
        assert_eq!(Provider::Anthropic.to_base_url(), ANTHROPIC_URL);
    }
}
