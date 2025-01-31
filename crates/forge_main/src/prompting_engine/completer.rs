use forge_domain::Command;
use reedline::{Completer, Span, Suggestion};

#[derive(Clone)]
pub struct CommandCompleter(Vec<String>);

impl Default for CommandCompleter {
    fn default() -> Self {
        Self(Command::available_commands())
    }
}

impl Completer for CommandCompleter {
    fn complete(&mut self, line: &str, _pos: usize) -> Vec<Suggestion> {
        self.0
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

#[cfg(test)]
mod tests {
    use super::*;

    impl CommandCompleter {
        fn new(commands: Vec<String>) -> Self {
            Self(commands)
        }

        fn test() -> Self {
            Self::new(vec!["/new".to_string(), "/end".to_string()])
        }
    }

    #[test]
    fn test_empty_input() {
        let mut completer = CommandCompleter::test();
        let suggestions = completer.complete("", 0);

        assert_eq!(suggestions.len(), 2);
    }

    #[test]
    fn test_partial_command() {
        let mut completer = CommandCompleter::test();
        let suggestions = completer.complete("/n", 0);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].value, "/new");
    }

    #[test]
    fn test_no_matches() {
        let mut completer = CommandCompleter::test();
        let suggestions = completer.complete("/xyz", 0);

        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_full_command() {
        let mut completer = CommandCompleter::test();
        let suggestions = completer.complete("/end", 0);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].value, "/end");
    }

    #[test]
    fn test_multiple_matches() {
        let mut completer = CommandCompleter::new(vec!["/new".to_string(), "/next".to_string()]);
        let suggestions = completer.complete("/n", 0);

        assert_eq!(suggestions.len(), 2);
        assert!(suggestions.iter().all(|s| s.value.starts_with("/n")));
    }

    #[test]
    fn test_suggestion_properties() {
        let mut completer = CommandCompleter::test();
        let suggestions = completer.complete("/end", 0);

        assert!(!suggestions.is_empty());
        let suggestion = &suggestions[0];

        assert!(suggestion.append_whitespace);
        assert_eq!(suggestion.description, None);
        assert_eq!(suggestion.style, None);
        assert_eq!(suggestion.extra, None);
    }
}
