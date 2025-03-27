use std::sync::Arc;
use std::time::Duration;

use indicatif::{MultiProgress, ProgressBar, ProgressStyle};

/// Creates and configures the progress indicators and UI elements for the CLI
/// application.
pub struct UI {
    multi_progress: Arc<MultiProgress>,
    success_prefix: &'static str,
}

impl UI {
    /// Creates a new UI instance.
    pub fn new() -> Self {
        UI {
            multi_progress: Arc::new(MultiProgress::new()),
            success_prefix: "\x1b[32m✓\x1b[0m", // Green checkmark with color reset
        }
    }

    /// Create a spinner style for in-progress tasks.
    pub fn create_spinner_style(&self) -> ProgressStyle {
        ProgressStyle::default_spinner()
            .tick_chars("⣾⣽⣻⢿⡿⣟⣯⣷")
            .template("{prefix:<2.cyan} {spinner:.blue} {wide_msg}")
            .unwrap()
    }

    /// Create a style for completed tasks.
    pub fn create_completion_style(&self) -> ProgressStyle {
        ProgressStyle::default_spinner()
            .template("{prefix:<2.cyan} {wide_msg}")
            .unwrap()
    }

    /// Create a new spinner with the given prefix and message.
    pub fn create_spinner(&self, prefix: String, message: String) -> ProgressBar {
        let spinner = self.multi_progress.add(ProgressBar::new_spinner());
        spinner.set_style(self.create_spinner_style());
        spinner.set_prefix(prefix);
        spinner.enable_steady_tick(Duration::from_millis(80));
        spinner.set_message(message);
        spinner
    }

    /// Update a spinner to show completion.
    pub fn complete_spinner(&self, spinner: &ProgressBar, message: String) {
        spinner.set_prefix(self.success_prefix);
        spinner.set_style(self.create_completion_style());
        spinner.finish_with_message(message);
    }
} 
