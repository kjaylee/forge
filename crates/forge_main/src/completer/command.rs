use reedline::{Completer, Span, Suggestion};

use crate::model::ForgeCommandManager;

#[derive(Clone)]
pub struct CommandCompleter(ForgeCommandManager);

impl CommandCompleter {
    pub fn new(command_manager: ForgeCommandManager) -> Self {
        Self(command_manager)
    }
}

impl Completer for CommandCompleter {
    fn complete(&mut self, line: &str, _: usize) -> Vec<reedline::Suggestion> {
        self.0
            .list()
            .into_iter()
            .filter(|cmd| cmd.name.starts_with(line))
            .map(|cmd| Suggestion {
                value: cmd.name,
                description: Some(cmd.description),
                style: None,
                extra: None,
                span: Span::new(0, line.len()),
                append_whitespace: true,
            })
            .collect()
    }
}
