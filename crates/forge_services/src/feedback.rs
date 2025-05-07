use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, RwLock}; // Use std::sync::RwLock instead of tokio::sync::RwLock

use anyhow::{anyhow, Context};
use forge_domain::{FeedbackService, FeedbackSettings};

pub struct ForgeFeedbackService {
    settings_path: PathBuf,
    settings: Arc<RwLock<FeedbackSettings>>,
}

impl ForgeFeedbackService {
    /// Create a new feedback service using synchronous operations
    pub fn new(base_path: PathBuf) -> anyhow::Result<Self> {
        let settings_dir = base_path.join("settings");

        // Create directory synchronously
        if !settings_dir.exists() {
            fs::create_dir_all(&settings_dir).context("Failed to create settings directory")?
        }

        let settings_path = settings_dir.join("feedback.json");
        let settings = if settings_path.exists() {
            match fs::read_to_string(&settings_path) {
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
        } else {
            FeedbackSettings::default()
        };

        Ok(Self { settings_path, settings: Arc::new(RwLock::new(settings)) })
    }

    /// Create a new service, falling back to default on error
    pub fn new_or_default(base_path: PathBuf) -> Self {
        match Self::new(base_path.clone()) {
            Ok(service) => service,
            Err(e) => {
                eprintln!("Error creating feedback service, falling back to default: {e}");
                Self::default(base_path)
            }
        }
    }

    pub fn default(base_path: PathBuf) -> Self {
        let settings_path = base_path.join("settings").join("feedback.json");
        Self {
            settings_path,
            settings: Arc::new(RwLock::new(FeedbackSettings::default())),
        }
    }

    /// Load feedback settings using std::fs synchronously, returning default
    /// settings on error
    fn load_settings(&self) -> FeedbackSettings {
        if !self.settings_path.exists() {
            return FeedbackSettings::default();
        }

        match fs::read_to_string(&self.settings_path) {
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

    /// Save settings using synchronous file operations
    fn save_settings(&self) -> anyhow::Result<()> {
        // Try to get a read lock
        let settings = match self.settings.read() {
            Ok(guard) => guard,
            Err(e) => {
                eprintln!("Failed to acquire read lock: {e:?}");
                return Ok(()); // Just return ok if we can't get the lock
            }
        };

        // Serialize the settings
        let content = match serde_json::to_string_pretty(&*settings) {
            Ok(content) => content,
            Err(e) => {
                return Err(anyhow!("Failed to serialize feedback settings: {}", e));
            }
        };

        // Ensure parent directory exists
        if let Some(parent) = self.settings_path.parent() {
            if !parent.exists() {
                fs::create_dir_all(parent).context("Failed to create settings directory")?
            }
        }

        // Write the file
        fs::write(&self.settings_path, content).context("Failed to write feedback settings")
    }

    // Synchronous version to check if feedback should be shown
    pub fn should_show_feedback_sync(&self) -> bool {
        match self.settings.read() {
            Ok(settings) => settings.should_show_feedback(),
            Err(_) => {
                // If we can't get the lock, read directly from disk
                let settings = self.load_settings();
                settings.should_show_feedback()
            }
        }
    }

    // Synchronous version to update the last shown timestamp
    pub fn update_last_shown_sync(&self) {
        // Update the settings in memory
        {
            if let Ok(mut settings) = self.settings.write() {
                settings.update_last_shown();
            } else {
                eprintln!("Failed to acquire write lock");
                return; // Just return if we can't update
            }
        }

        // Try to save settings, ignoring errors
        if let Err(e) = self.save_settings() {
            eprintln!("Failed to save feedback settings: {e}");
        }
    }
}

// Implement the FeedbackService trait for our synchronous service
#[async_trait::async_trait]
impl FeedbackService for ForgeFeedbackService {
    // Check if feedback should be shown
    async fn should_show_feedback(&self) -> anyhow::Result<bool> {
        // We're implementing a synchronous version, so we use sync operations
        Ok(self.should_show_feedback_sync())
    }

    // Update the last shown timestamp
    async fn update_last_shown(&self) -> anyhow::Result<()> {
        self.update_last_shown_sync();
        Ok(())
    }
}
