//! # Diff Formatting
//!
//! This module provides functionality for generating and displaying colorized
//! diffs in the terminal. It formats differences between text content with
//! line numbers and syntax highlighting to make changes clearly visible.
//!
//! ## Features
//!
//! * Line-by-line diff generation with context
//! * Syntax highlighting for additions, deletions, and unchanged lines
//! * Line number display for easier reference
//! * Support for both complete string output and streaming line-by-line output
//! * Integration with other display components for consistent styling

use std::fmt;
use std::path::PathBuf;

use console::{style, Style};
use similar::{ChangeTag, TextDiff};

use crate::TitleFormat;

struct Line(Option<usize>);

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            None => write!(f, "    "),
            Some(idx) => write!(f, "{:<4}", idx + 1),
        }
    }
}

pub struct DiffFormat;

impl DiffFormat {
    /// Creates a formatted diff as a complete string
    pub fn format(path: PathBuf, old: &str, new: &str) -> String {
        let diff = TextDiff::from_lines(old, new);
        let ops = diff.grouped_ops(3);

        let mut output = format!(
            "{}\n\n",
            TitleFormat::success("diff").sub_title(path.display().to_string())
        );

        if ops.is_empty() {
            output.push_str(&format!("{}\n", style("No changes applied").dim()));
            return output;
        }

        for (idx, group) in ops.iter().enumerate() {
            if idx > 0 {
                output.push_str(&format!("{}\n", style("...").dim()));
            }
            for op in group {
                for change in diff.iter_inline_changes(op) {
                    let (sign, s) = match change.tag() {
                        ChangeTag::Delete => ("-", Style::new().blue()),
                        ChangeTag::Insert => ("+", Style::new().yellow()),
                        ChangeTag::Equal => (" ", Style::new().dim()),
                    };

                    output.push_str(&format!(
                        "{}{} |{}",
                        style(Line(change.old_index())).dim(),
                        style(Line(change.new_index())).dim(),
                        s.apply_to(sign),
                    ));

                    for (_, value) in change.iter_strings_lossy() {
                        output.push_str(&format!("{}", s.apply_to(value)));
                    }
                    if change.missing_newline() {
                        output.push('\n');
                    }
                }
            }
        }
        output
    }

    /// Streams a diff line by line, calling the provided callback for each line
    /// 
    /// # Parameters
    /// 
    /// * `path` - The path of the file being compared
    /// * `old` - The original content
    /// * `new` - The new content
    /// * `line_callback` - A function that will be called for each line of the diff
    ///
    /// # Returns
    /// 
    /// * `()` - This function doesn't return anything
    pub fn stream<F>(path: PathBuf, old: &str, new: &str, mut line_callback: F)
    where
        F: FnMut(&str),
    {
        let diff = TextDiff::from_lines(old, new);
        let ops = diff.grouped_ops(3);

        // Output the header first
        let header = format!(
            "{}\n",
            TitleFormat::success("diff").sub_title(path.display().to_string())
        );
        line_callback(&header);
        line_callback("\n");

        if ops.is_empty() {
            line_callback(&format!("{}\n", style("No changes applied").dim()));
            return;
        }

        for (idx, group) in ops.iter().enumerate() {
            if idx > 0 {
                line_callback(&format!("{}\n", style("...").dim()));
            }
            for op in group {
                for change in diff.iter_inline_changes(op) {
                    let (sign, s) = match change.tag() {
                        ChangeTag::Delete => ("-", Style::new().blue()),
                        ChangeTag::Insert => ("+", Style::new().yellow()),
                        ChangeTag::Equal => (" ", Style::new().dim()),
                    };

                    let mut line = String::new();
                    
                    line.push_str(&format!(
                        "{}{} |{}",
                        style(Line(change.old_index())).dim(),
                        style(Line(change.new_index())).dim(),
                        s.apply_to(sign),
                    ));

                    for (_, value) in change.iter_strings_lossy() {
                        line.push_str(&format!("{}", s.apply_to(value)));
                    }
                    
                    line_callback(&line);
                    
                    if change.missing_newline() {
                        line_callback("\n");
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use console::strip_ansi_codes;
    use insta::assert_snapshot;

    use super::*;

    #[test]
    fn test_color_output() {
        let old = "Hello World\nThis is a test\nThird line\nFourth line";
        let new = "Hello World\nThis is a modified test\nNew line\nFourth line";
        let diff = DiffFormat::format("example.txt".into(), old, new);
        println!("\nColor Output Test:\n{}", diff);
    }

    #[test]
    fn test_diff_printer_no_differences() {
        let content = "line 1\nline 2\nline 3";
        let diff = DiffFormat::format("xyz.txt".into(), content, content);
        assert!(diff.contains("No changes applied"));
    }

    #[test]
    fn test_file_source() {
        let old = "line 1\nline 2\nline 3\nline 4\nline 5";
        let new = "line 1\nline 2\nline 3";
        let diff = DiffFormat::format("xya.txt".into(), old, new);
        let clean_diff = strip_ansi_codes(&diff);
        assert_snapshot!(clean_diff);
    }

    #[test]
    fn test_diff_printer_simple_diff() {
        let old = "line 1\nline 2\nline 3\nline 5\nline 6\nline 7\nline 8\nline 9";
        let new = "line 1\nmodified line\nline 3\nline 5\nline 6\nline 7\nline 8\nline 9";
        let diff = DiffFormat::format("abc.txt".into(), old, new);
        let clean_diff = strip_ansi_codes(&diff);
        assert_snapshot!(clean_diff);
    }
    
    #[test]
    fn test_stream_diff() {
        let old = "line 1\nline 2\nline 3\nline 4\nline 5";
        let new = "line 1\nline 2 modified\nline 3\nline 4\nnew line 5";
        
        let mut streamed_lines: Vec<String> = Vec::new();
        
        // Collect the streamed lines
        DiffFormat::stream("test_stream.txt".into(), old, new, |line| {
            streamed_lines.push(line.to_string());
        });
        
        // Also get the complete diff as a single string
        let complete_diff = DiffFormat::format("test_stream.txt".into(), old, new);
        
        // Strip ANSI codes from both for comparison
        let clean_streamed = streamed_lines
            .iter()
            .map(|line| strip_ansi_codes(line).to_string())
            .collect::<Vec<String>>()
            .join("");
            
        let clean_complete = strip_ansi_codes(&complete_diff);
        
        // The content should be the same, just delivered differently
        assert_eq!(clean_streamed, clean_complete);
    }
    
    #[test]
    fn test_stream_no_differences() {
        let content = "line 1\nline 2\nline 3";
        
        let mut streamed_lines: Vec<String> = Vec::new();
        
        DiffFormat::stream("xyz.txt".into(), content, content, |line| {
            streamed_lines.push(line.to_string());
        });
        
        // Join all lines and check for the "No changes applied" message
        let joined = streamed_lines.join("");
        assert!(joined.contains("No changes applied"));
    }
}
