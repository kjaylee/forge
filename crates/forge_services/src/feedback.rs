use std::path::PathBuf;

use anyhow::anyhow;
use forge_domain::{FeedbackService, FeedbackSettings};
use forge_fs::ForgeFS;

pub struct ForgeFeedbackService {
    settings_path: PathBuf,
}

impl ForgeFeedbackService {
    pub fn new(base_path: PathBuf) -> Self {
        let settings_path = base_path.join("settings").join("feedback.json");
        Self {
            settings_path,
        }
    }

    /// Load feedback settings from the file, returning default settings if any error occurs
    async fn load_settings(&self) -> FeedbackSettings {
        if !ForgeFS::exists(&self.settings_path) {
            return FeedbackSettings::default();
        }

        match ForgeFS::read_to_string(&self.settings_path).await {
            Ok(content) => match serde_json::from_str(&content) {
                Ok(settings) => settings,
                Err(e) => {
                    eprintln!("Failed to parse feedback settings: {e}");
                    FeedbackSettings::default()
                }
            },
            Err(e) => {
                eprintln!("Failed to read feedback settings: {e}");
                FeedbackSettings::default()
            }
        }
    }

    /// Save the provided settings to disk
    async fn save_settings(&self, settings: &FeedbackSettings) -> anyhow::Result<()> {
        // Serialize the settings
        let content = match serde_json::to_string_pretty(settings) {
            Ok(content) => content,
            Err(e) => {
                return Err(anyhow!("Failed to serialize feedback settings: {}", e));
            }
        };
        
        // Ensure parent directory exists
        if let Some(parent) = self.settings_path.parent() {
            if !ForgeFS::exists(parent) {
                ForgeFS::create_dir_all(parent).await?
            }
        }
        
        // Write the file
        ForgeFS::write(&self.settings_path, content).await
    }

    // Methods below are now inlined directly in the FeedbackService implementation
}

// Implement the FeedbackService trait for our async service
#[async_trait::async_trait]
impl FeedbackService for ForgeFeedbackService {
    // Check if feedback should be shown - always reads from disk
    async fn should_show_feedback(&self) -> anyhow::Result<bool> {
        // Read settings from disk
        let settings = self.load_settings().await;
        
        // Return whether feedback should be shown
        Ok(settings.should_show_feedback())
    }

    // Update the last shown timestamp
    async fn update_last_shown(&self) -> anyhow::Result<()> {
        // Load current settings from disk
        let mut settings = self.load_settings().await;
        
        // Update the timestamp
        settings.update_last_shown();
        
        // Save the updated settings back to disk
        self.save_settings(&settings).await
    }
}
