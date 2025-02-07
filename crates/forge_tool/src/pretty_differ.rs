use std::fmt;
use std::path::{Path, PathBuf};

use console::{style, Style};
use similar::{ChangeTag, TextDiff};

struct Line(Option<usize>);

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            None => write!(f, "    "),
            Some(idx) => write!(f, "{:<4}", idx + 1),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Source {
    /// Content from a file path
    Path { path: PathBuf, content: String },
    /// Direct string content
    Content(String),
}

impl Default for Source {
    fn default() -> Self {
        Source::Content(String::new())
    }
}

impl From<String> for Source {
    fn from(content: String) -> Self {
        Source::Content(content)
    }
}

impl Source {
    pub async fn from_path(path: PathBuf) -> std::io::Result<Self> {
        let content = tokio::fs::read_to_string(&path).await?;
        Ok(Source::Path { path, content })
    }

    /// Get the content of the source
    pub fn content(&self) -> &str {
        match self {
            Source::Path { content, .. } => content,
            Source::Content(content) => content,
        }
    }

    /// Get the path if this source
    pub fn path(&self) -> Option<&Path> {
        match self {
            Source::Path { path, .. } => Some(path),
            Source::Content(_) => None,
        }
    }
}

pub struct PrettyDiffer {
    old: Source,
    new: Source,
}

impl PrettyDiffer {
    pub fn new(old: Source, new: Source) -> Self {
        PrettyDiffer { old, new }
    }

    /// Display the paths if they exist.
    fn format_file_paths_section(
        &self,
        old_path: Option<&Path>,
        new_path: Option<&Path>,
        mut output: String,
    ) -> String {
        // Only show file paths section if at least one path is present
        if old_path.is_some() || new_path.is_some() {
            output.push('\n');
            match (old_path, new_path) {
                (Some(old), Some(new)) => {
                    // Check if paths are the same
                    if old == new {
                        output.push_str(&format!(
                            "{} {}",
                            style("File: ").bold(),
                            style(old.display()).dim()
                        ));
                    } else {
                        // Different paths
                        output.push_str(&format!(
                            "{} {}\n",
                            style("Old:").bold(),
                            style(old.display()).dim()
                        ));
                        output.push_str(&format!(
                            "{} {}",
                            style("New:").bold(),
                            style(new.display()).dim()
                        ));
                    }
                }
                (Some(path), None) | (None, Some(path)) => {
                    // Only one path available
                    output.push_str(&format!(
                        "{} {}",
                        style("File:").bold(),
                        style(path.display()).dim()
                    ));
                }
                _ => {}
            }
            output.push('\n');
        }
        output
    }

    pub fn format(&self) -> String {
        let old_content = self.old.content();
        let new_content = self.new.content();
        let new_file_path = self.new.path();
        let old_file_path = self.old.path();

        let diff = TextDiff::from_lines(old_content, new_content);
        let ops = diff.grouped_ops(3);

        let mut output =
            self.format_file_paths_section(old_file_path, new_file_path, String::new());
        if ops.is_empty() {
            output.push_str(&format!("{}\n", style("No changes found").dim()));
            return output;
        }

        for (idx, group) in ops.iter().enumerate() {
            if idx > 0 {
                output.push_str(&format!("{}\n", style("...").dim()));
            }
            for op in group {
                for change in diff.iter_inline_changes(op) {
                    let (sign, s) = match change.tag() {
                        ChangeTag::Delete => ("-", Style::new().red()),
                        ChangeTag::Insert => ("+", Style::new().green()),
                        ChangeTag::Equal => (" ", Style::new().dim()),
                    };

                    output.push_str(&format!(
                        "{}{} |{}",
                        style(Line(change.old_index())).dim(),
                        style(Line(change.new_index())).dim(),
                        s.apply_to(sign).bold(),
                    ));

                    for (emphasized, value) in change.iter_strings_lossy() {
                        if emphasized {
                            output.push_str(&format!(
                                "{}",
                                s.apply_to(value).underlined().on_black()
                            ));
                        } else {
                            output.push_str(&format!("{}", s.apply_to(value)));
                        }
                    }
                    if change.missing_newline() {
                        output.push('\n');
                    }
                }
            }
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use console::strip_ansi_codes;
    use insta::assert_snapshot;

    use super::*;

    #[test]
    fn test_diff_printer_no_differences() {
        let content = "line 1\nline 2\nline 3";
        let old = Source::Content(content.to_string());
        let new = Source::Content(content.to_string());
        let printer = PrettyDiffer::new(old, new);
        let diff = printer.format();
        assert!(diff.contains("No changes found"));
    }

    #[test]
    fn test_file_source() {
        let old = Source::Path {
            path: "text.txt".into(),
            content: "line 1\nline 2\nline 3\nline 4\nline 5".to_string(),
        };
        let new = Source::Content("line 1\nline 2\nline 3".to_string());
        let printer = PrettyDiffer::new(old, new);
        let diff = printer.format();
        let clean_diff = strip_ansi_codes(&diff);
        assert_snapshot!(clean_diff);
    }

    #[test]
    fn test_diff_printer_simple_diff() {
        let old = Source::Content(
            "line 1\nline 2\nline 3\nline 5\nline 6\nline 7\nline 8\nline 9".to_string(),
        );
        let new = Source::Content(
            "line 1\nmodified line\nline 3\nline 5\nline 6\nline 7\nline 8\nline 9".to_string(),
        );
        let printer = PrettyDiffer::new(old, new);
        let diff = printer.format();
        let clean_diff = strip_ansi_codes(&diff);
        assert_snapshot!(clean_diff);
    }
}
