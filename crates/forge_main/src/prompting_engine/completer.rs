use std::path::PathBuf;

use forge_domain::Command;
use forge_walker::Walker;
use reedline::{Completer, Span, Suggestion};

#[derive(Clone)]
pub struct ReedlineCompleter {
    walker: Walker,
}

impl ReedlineCompleter {
    pub fn new(cwd: PathBuf) -> Self {
        let walker = Walker::max_all().cwd(cwd).skip_binary(true);
        Self { walker }
    }
}

impl Completer for ReedlineCompleter {
    fn complete(&mut self, line: &str, _: usize) -> Vec<Suggestion> {
        // For command completion
        if line.starts_with('/') {
            return Command::available_commands()
                .into_iter()
                .filter(|cmd| cmd.starts_with(line))
                .map(|cmd| Suggestion {
                    value: cmd,
                    description: None,
                    style: None,
                    extra: None,
                    span: Span::new(0, line.len()),
                    append_whitespace: true,
                })
                .collect();
        }

        // For file completion - find the last @ and use everything after it as the
        // search term
        if let Some(last_at_pos) = line.rfind('@') {
            let search_term = &line[(last_at_pos + 1)..];
            let files = self.walker.get_blocking().unwrap_or_default();
            files
                .into_iter()
                .filter(|file| !file.is_dir())
                .filter_map(|file| {
                    if !search_term.is_empty()
                        && file
                            .file_name
                            .as_ref()
                            .map_or_else(|| false, |file| file.contains(search_term))
                    {
                        Some(Suggestion {
                            value: format!("@{}", file.path),
                            description: if file.is_dir() {
                                Some("Directory".to_string())
                            } else {
                                Some("File".to_string())
                            },
                            style: None,
                            extra: None,
                            span: Span::new(last_at_pos, line.len()),
                            append_whitespace: true,
                        })
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            // No completion for other inputs
            Vec::new()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs::{self, File};

    use tempfile::tempdir;

    use super::*;

    #[test]
    fn test_empty_input_commands() {
        let mut completer = ReedlineCompleter::new(PathBuf::from("."));
        let suggestions = completer.complete("/", 0);

        // Should return all available commands
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().all(|s| s.value.starts_with('/')));
    }

    #[test]
    fn test_partial_command() {
        let mut completer = ReedlineCompleter::new(PathBuf::from("."));
        let suggestions = completer.complete("/n", 0);

        // Should return commands starting with /n
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().all(|s| s.value.starts_with("/n")));
    }

    #[test]
    fn test_no_completion_for_regular_text() {
        let mut completer = ReedlineCompleter::new(PathBuf::from("."));
        let suggestions = completer.complete("regular", 0);

        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_file_completion() {
        let dir = tempdir().unwrap();
        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();

        let mut completer = ReedlineCompleter::new(dir.path().to_path_buf());
        let suggestions = completer.complete("@test", 0);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].value, "@test.txt");
        assert_eq!(suggestions[0].description, Some("File".to_string()));
    }

    #[test]
    fn test_file_completion_empty() {
        let dir = tempdir().unwrap();
        let mut completer = ReedlineCompleter::new(dir.path().to_path_buf());
        let suggestions = completer.complete("@", 0);

        // Should list all files/directories in the empty temp directory
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_file_completion_multiple_at() {
        let dir = tempdir().unwrap();
        let file_path = dir.path().join("test.txt");
        File::create(&file_path).unwrap();

        let mut completer = ReedlineCompleter::new(dir.path().to_path_buf());
        // Using multiple @ characters, only the last one should be used for search
        let suggestions = completer.complete("some@text@test", 0);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].value, "@test.txt");
        assert_eq!(suggestions[0].description, Some("File".to_string()));
    }
}
