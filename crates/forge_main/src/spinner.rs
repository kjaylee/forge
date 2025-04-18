use std::time::Instant;

use anyhow::Result;
use colored::Colorize;
use rand::seq::SliceRandom;
use spinoff::spinners::Dots8;
use spinoff::{Color, Spinner};

/// Manages spinner functionality for the UI
#[derive(Default)]
pub struct SpinnerManager {
    spinner: Option<Spinner>,
    start_time: Option<Instant>,
    message: Option<String>,
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
        let word = words.choose(&mut rand::thread_rng()).unwrap_or(&words[0]);
        let cancel_message = "Ctrl+C to interrupt".white().dimmed();
        let updated_message = format!("{} 0s · {}", word.green().bold(), cancel_message);

        // Store the base message without styling for later use with the timer
        self.message = Some(word.to_string());

        // Initialize the start time for the timer
        self.start_time = Some(Instant::now());

        // Create and start a new spinner
        let spinner = Spinner::new(Dots8, updated_message, Color::Green);
        self.spinner = Some(spinner);

        Ok(())
    }

    /// Update the spinner with the current elapsed time
    pub fn update_time(&mut self) -> Result<()> {
        if let (Some(start_time), Some(message), Some(spinner)) =
            (self.start_time, self.message.as_ref(), &mut self.spinner)
        {
            let elapsed = start_time.elapsed();
            let seconds = elapsed.as_secs();
            let cancel_message = "Ctrl+C to interrupt".white().dimmed();
            // Update the spinner text with the elapsed time
            let updated_message = format!(
                "{} {}s · {}",
                message.green().bold(),
                seconds,
                cancel_message
            );
            spinner.update_text(updated_message);
        }
        Ok(())
    }

    /// Stop the active spinner if any
    pub fn stop(&mut self, message: Option<String>) -> Result<()> {
        if let Some(mut spinner) = self.spinner.take() {
            if let Some(msg) = message.clone() {
                spinner.stop_with_message(&msg);
            } else {
                spinner.stop();
            }
        } else if let Some(message) = message {
            println!("{}", message);
        }

        self.start_time = None;
        self.message = None;
        Ok(())
    }
}
