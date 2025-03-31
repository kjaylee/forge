use forge_api::Usage;

use crate::application::PromptContext;
use crate::domain::ForgeMode;

#[derive(Default)]
pub struct PromptFormatter {
    title: Option<String>,
    usage: Option<Usage>,
    mode: Option<ForgeMode>,
}

impl PromptFormatter {
    pub fn title(mut self, title: impl ToString) -> Self {
        self.title = Some(title.to_string());
        self
    }

    pub fn usage(mut self, usage: Usage) -> Self {
        self.usage = Some(usage);
        self
    }

    pub fn mode(mut self, mode: ForgeMode) -> Self {
        self.mode = Some(mode);
        self
    }

    pub fn to_context(&self) -> PromptContext {
        PromptContext::new()
            .with_title(self.title.clone().unwrap_or_default())
            .with_usage(self.usage.clone().unwrap_or_default())
            .with_mode(
                self.mode
                    .clone()
                    .unwrap_or_else(|| ForgeMode::new("DEFAULT")),
            )
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_prompt_formatter() {
        let fixture = PromptFormatter::default()
            .title("Test Title")
            .usage(Usage::default())
            .mode(ForgeMode::new("TEST"));

        let context = fixture.to_context();

        assert_eq!(context.title, Some("Test Title".to_string()));
        assert!(context.usage.is_some());
        assert_eq!(context.mode.unwrap(), "TEST");
    }
}
