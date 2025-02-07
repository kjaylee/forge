use std::{
    fmt,
    path::{Path, PathBuf},
};

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

#[derive(Default)]
pub struct DiffPrinter {
    old_content: String,
    new_content: String,
    old_path: Option<PathBuf>,
    new_path: Option<PathBuf>,
}

impl DiffPrinter {
    /// reads the path if it exists.
    pub async fn old_path(mut self, path: &Path) -> std::io::Result<Self> {
        if path.exists() {
            self.old_path = Some(path.to_path_buf());
            self.old_content = tokio::fs::read_to_string(path).await?;
        }
        Ok(self)
    }

    /// reads the path if it exists.
    pub async fn new_path(mut self, path: &Path) -> std::io::Result<Self> {
        if path.exists() {
            self.new_path = Some(path.to_path_buf());
            self.new_content = tokio::fs::read_to_string(path).await?;
        }
        Ok(self)
    }

    /// Display the paths if they exist.
    fn display_file_name(&self, mut output: String) -> String {
        // Only show file paths section if at least one path is present
        if self.old_path.is_some() || self.new_path.is_some() {
            output.push_str(&format!(
                "\n{}\n",
                style("┌─── File Changes ").bold().cyan()
            ));

            match (self.old_path.as_deref(), self.new_path.as_deref()) {
                (Some(old), Some(new)) => {
                    // Check if paths are the same
                    if old == new {
                        output.push_str(&format!(
                            "{}  {} {}\n",
                            style("│").bold().cyan(),
                            style("Path:").dim(),
                            style(old.display()).bold().underlined()
                        ));
                        output.push_str(&format!("{}\n", style("│").bold().cyan(),));
                    } else {
                        // Different paths
                        output.push_str(&format!(
                            "{}  {} {}\n",
                            style("│").bold().cyan(),
                            style("Old:").dim(),
                            style(old.display()).bold().underlined()
                        ));
                        output.push_str(&format!(
                            "{}  {} {}\n",
                            style("│").bold().cyan(),
                            style("New:").dim(),
                            style(new.display()).bold().underlined()
                        ));
                    }
                }
                (Some(path), None) | (None, Some(path)) => {
                    // Only one path available
                    output.push_str(&format!(
                        "{}  {} {}\n",
                        style("│").bold().cyan(),
                        style("Path:").dim(),
                        style(path.display()).bold().underlined()
                    ));
                }
                _ => {
                    // no-op, we won't reach here bcoz of the if condition
                }
            }

            output.push_str(&format!("{}\n", style("└───────────────").bold().cyan()));
        }
        output
    }

    pub fn diff(&self) -> String {
        let diff = TextDiff::from_lines(&self.old_content, &self.new_content);

        let mut output = self.display_file_name(String::new());

        for (idx, group) in diff.grouped_ops(3).iter().enumerate() {
            if idx > 0 {
                output.push_str(&format!("{:-^1$}\n", "-", 80));
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
