use std::path::PathBuf;

use async_trait::async_trait;

use crate::error::Result;
use crate::Error;

/// Represents user input types in the chat application.
///
/// This enum encapsulates all forms of input including:
/// - System commands (starting with '/')
/// - Regular chat messages
/// - File content
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// End the current session and exit the application.
    /// This can be triggered with the '/end' command.
    End,
    /// Start a new conversation while preserving history.
    /// This can be triggered with the '/new' command.
    New,
    /// Reload the conversation with the original prompt.
    /// This can be triggered with the '/reload' command.
    Reload,
    /// A regular text message from the user to be processed by the chat system.
    /// Any input that doesn't start with '/' is treated as a message.
    Message(String),
    /// Display system environment information.
    /// This can be triggered with the '/info' command.
    Info,
    /// Exit the application without any further action.
    Exit,
    /// Config command, can be used to get or set or display configuration
    /// values.
    Config(ConfigCommand),
}

/// Represents different configuration operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigCommand {
    /// List all available configuration options
    List,
    /// Get the value of a specific configuration key
    Get(String),
    /// Set a configuration key to a specific value
    Set(String, String),
}

impl ConfigCommand {
    /// Parse a config command from string arguments
    ///
    /// # Arguments
    /// * `args` - Command arguments (without "config" command itself)
    ///
    /// # Returns
    /// * `Ok(ConfigCommand)` - Successfully parsed command
    /// * `Err` - Parse error with usage information
    fn parse(args: &[&str]) -> Result<ConfigCommand> {
        // No arguments = list command
        if args.is_empty() {
            return Ok(ConfigCommand::List);
        }

        // Get command type and ensure it's valid
        match args.first().copied() {
            Some("get") => {
                let key = args
                    .get(1)
                    .ok_or_else(|| Error::CommandParse("Usage: /config get <key>".into()))?;
                Ok(ConfigCommand::Get(key.to_string()))
            }
            Some("set") => {
                let key = args.get(1).ok_or_else(|| {
                    Error::CommandParse("Usage: /config set <key> <value>".into())
                })?;
                let value = args
                    .get(2..)
                    .filter(|rest| !rest.is_empty())
                    .ok_or_else(|| Error::CommandParse("Usage: /config set <key> <value>".into()))?
                    .join(" ");

                if value.is_empty() {
                    return Err(Error::CommandParse("Value cannot be empty".into()));
                }

                Ok(ConfigCommand::Set(key.to_string(), value))
            }
            _ => Err(Error::CommandParse(
                "Usage: /config [get <key> | set <key> <value>]".into(),
            )),
        }
    }
}

impl Command {
    /// Returns a list of all available command strings.
    ///
    /// These commands are used for:
    /// - Command validation
    /// - Autocompletion
    /// - Help display
    pub fn available_commands() -> Vec<String> {
        vec![
            "/end".to_string(),
            "/new".to_string(),
            "/reload".to_string(),
            "/info".to_string(),
            "/exit".to_string(),
            "/config".to_string(),
            "/config set".to_string(),
            "/config get".to_string(),
        ]
    }

    /// Parses a string input into an Input.
    ///
    /// This function:
    /// - Trims whitespace from the input
    /// - Recognizes and validates commands (starting with '/')
    /// - Converts regular text into messages
    ///
    /// # Returns
    /// - `Ok(Input)` - Successfully parsed input
    /// - `Err` - Input was an invalid command
    pub fn parse(input: &str) -> Result<Self> {
        let trimmed = input.trim();

        // Handle config commands
        if trimmed.starts_with("/config") {
            let args: Vec<&str> = trimmed.split_whitespace().skip(1).collect();
            return Ok(Command::Config(ConfigCommand::parse(&args)?));
        }

        match trimmed {
            "/end" => Ok(Command::End),
            "/new" => Ok(Command::New),
            "/reload" => Ok(Command::Reload),
            "/info" => Ok(Command::Info),
            "/exit" => Ok(Command::Exit),
            text => Ok(Command::Message(text.to_string())),
        }
    }
}

/// A trait for handling user input in the application.
///
/// This trait defines the core functionality needed for processing
/// user input, whether it comes from a command line interface,
/// GUI, or file system.
#[async_trait]
pub trait UserInput {
    type PromptInput;
    /// Read content from a file and convert it to the input type.
    ///
    /// # Arguments
    /// * `path` - The path to the file to read
    ///
    /// # Returns
    /// * `Ok(Input)` - Successfully read and parsed file content
    /// * `Err` - Failed to read or parse file
    async fn upload<P: Into<PathBuf> + Send>(&self, path: P) -> anyhow::Result<Command>;

    /// Prompts for user input with optional help text and initial value.
    ///
    /// # Arguments
    /// * `help_text` - Optional help text to display with the prompt
    /// * `initial_text` - Optional initial text to populate the input with
    ///
    /// # Returns
    /// * `Ok(Input)` - Successfully processed input
    /// * `Err` - An error occurred during input processing
    async fn prompt(&self, input: Option<Self::PromptInput>) -> anyhow::Result<Command>;
}

#[cfg(test)]
mod tests {
    use super::*;

    mod config_command {
        use super::*;

        #[test]
        fn parse_empty_args_returns_list() {
            let args: Vec<&str> = vec![];
            let cmd = ConfigCommand::parse(&args).unwrap();
            assert!(matches!(cmd, ConfigCommand::List));
        }

        #[test]
        fn parse_get_command_with_key() {
            let args = vec!["get", "test-key"];
            let cmd = ConfigCommand::parse(&args).unwrap();
            assert!(matches!(cmd, ConfigCommand::Get(key) if key == "test-key"));
        }

        #[test]
        fn parse_get_command_without_key_returns_error() {
            let args = vec!["get"];
            let err = ConfigCommand::parse(&args).unwrap_err();
            assert!(matches!(err, Error::CommandParse(msg) if msg.contains("Usage")));
        }

        #[test]
        fn parse_set_command_with_key_value() {
            let args = vec!["set", "test-key", "test value with spaces"];
            let cmd = ConfigCommand::parse(&args).unwrap();
            assert!(matches!(cmd, ConfigCommand::Set(key, value) 
                if key == "test-key" && value == "test value with spaces"));
        }

        #[test]
        fn parse_set_command_without_value_returns_error() {
            let args = vec!["set", "test-key"];
            let err = ConfigCommand::parse(&args).unwrap_err();
            assert!(matches!(err, Error::CommandParse(msg) if msg.contains("Usage")));
        }

        #[test]
        fn parse_set_command_without_key_returns_error() {
            let args = vec!["set"];
            let err = ConfigCommand::parse(&args).unwrap_err();
            assert!(matches!(err, Error::CommandParse(msg) if msg.contains("Usage")));
        }

        #[test]
        fn parse_set_command_with_empty_value_returns_error() {
            let args = vec!["set", "test-key", ""];
            let err = ConfigCommand::parse(&args).unwrap_err();
            assert!(matches!(err, Error::CommandParse(msg) if msg.contains("empty")));
        }

        #[test]
        fn parse_invalid_command_returns_error() {
            let args = vec!["invalid"];
            let err = ConfigCommand::parse(&args).unwrap_err();
            assert!(matches!(err, Error::CommandParse(msg) if msg.contains("Usage")));
        }

        #[test]
        fn parse_set_preserves_value_whitespace() {
            let args = vec!["set", "test-key", "value", "with", "  multiple  ", "spaces"];
            let cmd = ConfigCommand::parse(&args).unwrap();
            assert!(matches!(cmd, ConfigCommand::Set(key, value) 
                if key == "test-key" && value == "value with   multiple   spaces"));
        }
    }

    mod command_parsing {
        use super::*;

        #[test]
        fn parse_config_list() {
            let result = Command::parse("/config").unwrap();
            assert!(matches!(result, Command::Config(ConfigCommand::List)));
        }

        #[test]
        fn parse_config_get() {
            let result = Command::parse("/config get key").unwrap();
            assert!(matches!(result, Command::Config(ConfigCommand::Get(key)) if key == "key"));
        }

        #[test]
        fn parse_config_set_single_value() {
            let result = Command::parse("/config set key value").unwrap();
            assert!(
                matches!(result, Command::Config(ConfigCommand::Set(key, value)) 
                if key == "key" && value == "value")
            );
        }

        #[test]
        fn parse_config_set_multiple_words() {
            let result = Command::parse("/config set key multiple words").unwrap();
            assert!(
                matches!(result, Command::Config(ConfigCommand::Set(key, value)) 
                if key == "key" && value == "multiple words")
            );
        }
    }
}
