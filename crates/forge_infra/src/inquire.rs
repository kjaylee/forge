use anyhow::{anyhow, Result};
use forge_services::InquireService;
use inquire::ui::{RenderConfig, Styled};

pub struct ForgeInquire;

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
    async fn select_one(&self, message: &str, options: Vec<String>) -> Result<String> {
        // We need to use tokio::task::spawn_blocking because inquire is blocking
        // and we're in an async context
        let message_owned = message.to_string();
        let selected = tokio::task::spawn_blocking(move || {
            inquire::Select::new(&message_owned, options)
                .with_render_config(Self::render_config())
                .with_help_message("Use arrow keys to navigate, Enter to select")
                .prompt()
        })
        .await
        .map_err(|e| anyhow!("Failed to spawn blocking task: {}", e))??;

        Ok(selected)
    }

    async fn select_many(&self, message: &str, options: Vec<String>) -> Result<Vec<String>> {
        let message_owned = message.to_string();
        let selected = tokio::task::spawn_blocking(move || {
            inquire::MultiSelect::new(&message_owned, options)
                .with_render_config(Self::render_config())
                .with_help_message(
                    "Use arrow keys to navigate, Space to select/deselect, Enter to confirm",
                )
                .prompt()
        })
        .await
        .map_err(|e| anyhow!("Failed to spawn blocking task: {}", e))??;

        Ok(selected)
    }
}
