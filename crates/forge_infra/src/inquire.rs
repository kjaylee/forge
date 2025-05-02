use anyhow::{anyhow, Result};
use forge_services::InquireService;
use inquire::ui::{RenderConfig, Styled};

pub struct ForgeInquire;

impl Default for ForgeInquire {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeInquire {
    pub fn new() -> Self {
        Self
    }

    fn render_config() -> RenderConfig {
        RenderConfig::default()
            .with_scroll_up_prefix(Styled::new("⇡"))
            .with_scroll_down_prefix(Styled::new("⇣"))
            .with_highlighted_option_prefix(Styled::new("➤"))
    }
}

#[async_trait::async_trait]
impl InquireService for ForgeInquire {
    async fn prompt_question(&self, question: &str) -> anyhow::Result<Option<String>> {
        let question_owned = question.to_string();
        let answer = tokio::task::spawn_blocking(move || {
            inquire::Text::new(&question_owned)
                .with_render_config(Self::render_config())
                .with_help_message("Press Enter to submit, ESC to cancel")
                .prompt()
        })
        .await
        .map_err(|e| anyhow!("Failed to spawn blocking task for prompt_question: {}", e))?;

        // Handle user interruption (inquire returns Err with
        // inquire::InquireError::OperationCanceled)
        match answer {
            Ok(text) => Ok(Some(text)),
            Err(inquire::InquireError::OperationCanceled) => Ok(None),
            Err(e) => Err(anyhow!(e)),
        }
    }

    async fn select_one(&self, message: &str, options: Vec<String>) -> Result<Option<String>> {
        // We need to use tokio::task::spawn_blocking because inquire is blocking
        // and we're in an async context
        let message_owned = message.to_string();
        let selected = tokio::task::spawn_blocking(move || {
            inquire::Select::new(&message_owned, options)
                .with_render_config(Self::render_config())
                .with_help_message("Use arrow keys to navigate, Enter to select, ESC to cancel")
                .prompt()
        })
        .await
        .map_err(|e| anyhow!("Failed to spawn blocking task: {}", e))?;

        // Handle user interruption
        match selected {
            Ok(selection) => Ok(Some(selection)),
            Err(inquire::InquireError::OperationCanceled) => Ok(None),
            Err(e) => Err(anyhow!(e)),
        }
    }

    async fn select_many(
        &self,
        message: &str,
        options: Vec<String>,
    ) -> Result<Option<Vec<String>>> {
        let message_owned = message.to_string();
        let selected = tokio::task::spawn_blocking(move || {
            inquire::MultiSelect::new(&message_owned, options)
                .with_render_config(Self::render_config())
                .with_help_message(
                    "Use arrow keys to navigate, Space to select/deselect, Enter to confirm, ESC to cancel",
                )
                .prompt()
        })
        .await
        .map_err(|e| anyhow!("Failed to spawn blocking task: {}", e))?;

        // Handle user interruption
        match selected {
            Ok(selections) => Ok(Some(selections)),
            Err(inquire::InquireError::OperationCanceled) => Ok(None),
            Err(e) => Err(anyhow!(e)),
        }
    }
}
