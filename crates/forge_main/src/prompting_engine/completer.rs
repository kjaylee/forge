use forge_domain::Command;
use reedline::{Completer, Span, Suggestion};

#[derive(Clone)]
pub struct CommandCompleter {
    commands: Vec<String>,
}

impl Default for CommandCompleter {
    fn default() -> Self {
        Self { commands: Command::available_commands() }
    }
}

impl Completer for CommandCompleter {
    fn complete(&mut self, line: &str, _pos: usize) -> Vec<Suggestion> {
        self.commands
            .iter()
            .filter(|cmd| cmd.starts_with(line))
            .map(|cmd| Suggestion {
                value: cmd.to_string(),
                description: None,
                style: None,
                extra: None,
                span: Span::new(0, line.len()),
                append_whitespace: true,
            })
            .collect()
    }
}
