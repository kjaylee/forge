use reqwest::Url;

/// A underlying provider for the open router.
#[derive(Clone, Debug)]
pub enum Provider {
    OpenAI,
    OpenRouter,
    Antinomy,
}

impl Provider {
    pub fn is_openai(&self) -> bool {
        matches!(self, Self::OpenAI) || matches!(self, Self::Antinomy)
    }

    pub fn is_open_router(&self) -> bool {
        matches!(self, Self::OpenRouter)
    }

    pub fn base_url(&self) -> Url {
        match self {
            Self::OpenAI => "https://api.openai.com/v1/".parse().unwrap(),
            Self::OpenRouter => "https://openrouter.ai/api/v1/".parse().unwrap(),
            Self::Antinomy => "https://antinomy.ai/api/v1/".parse().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_provider_parser() {
        assert_eq!(
            Provider::OpenAI.base_url(),
            "https://api.openai.com/v1/".parse().unwrap()
        );
        assert_eq!(
            Provider::OpenRouter.base_url(),
            "https://openrouter.ai/api/v1/".parse().unwrap()
        );
        assert_eq!(
            Provider::Antinomy.base_url(),
            "https://antinomy.ai/api/v1/".parse().unwrap()
        );
    }
}
