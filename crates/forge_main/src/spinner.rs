use anyhow::Result;
use colored::Colorize;
use rand::seq::SliceRandom;
use spinners::{Spinner, Spinners};

use crate::console::CONSOLE;

/// Manages spinner functionality for the UI
#[derive(Default)]
pub struct SpinnerManager {
    spinner: Option<Spinner>,
}

impl SpinnerManager {
    pub fn new() -> Self {
        Self::default()
    }

    /// Start the spinner with a message
    pub fn start(&mut self) -> Result<()> {
        self.stop(None)?;
        let words = vec![
            "Unfolding",
            "Ripening",
            "Emerging",
            "Stirring",
            "Dwelling",
            "Gesturing",
            "Thinking",
            "Processing",
            "Forging",
            "Tracing",
            "Seeking",
            "Hovering",
            "Yearning",
            "Glimpsing",
        ];

        // Use a random word from the list followed by ...
        let message = words.choose(&mut rand::thread_rng()).unwrap_or(&words[0]);
        let cancel_message = "(press Ctrl+C to stop & Ctrl+D to exit)".dimmed();
        let message = format!("{} {}", message, cancel_message);
        // Create and start a new spinner
        let spinner = Spinner::with_timer(Spinners::Dots8, message.green().bold().to_string());
        self.spinner = Some(spinner);

        Ok(())
    }

    /// Stop the active spinner if any
    pub fn stop(&mut self, message: Option<String>) -> Result<()> {
        if let Some(mut spinner) = self.spinner.take() {
            spinner.stop_with_message(message.unwrap_or_default().to_string());
        } else if let Some(message) = message {
            CONSOLE.writeln(message)?;
        }
        Ok(())
    }
}
