use std::path::{Path, PathBuf};

use derive_setters::Setters;

use crate::utils::format_match;
use crate::{FsCreateService, Match};

pub async fn create_temp_file<S: FsCreateService>(
    services: &S,
    prefix: &str,
    ext: &str,
    content: &str,
) -> anyhow::Result<PathBuf> {
    let path = tempfile::Builder::new()
        .disable_cleanup(true)
        .prefix(prefix)
        .suffix(ext)
        .tempfile()?
        .into_temp_path()
        .to_path_buf();
    services
        .create(
            path.to_string_lossy().to_string(),
            content.to_string(),
            true,
            false,
        )
        .await?;
    Ok(path)
}

/// Clips text content based on line count
fn clip_by_lines(
    content: &str,
    prefix_lines: usize,
    suffix_lines: usize,
) -> (Vec<String>, Option<(usize, usize)>) {
    let lines: Vec<&str> = content.lines().collect();
    let total_lines = lines.len();

    // If content fits within limits, return all lines
    if total_lines <= prefix_lines + suffix_lines {
        return (lines.into_iter().map(String::from).collect(), None);
    }

    // Collect prefix and suffix lines
    let mut result_lines = Vec::new();

    // Add prefix lines
    for line in lines.iter().take(prefix_lines) {
        result_lines.push(line.to_string());
    }

    // Add suffix lines
    for line in lines.iter().skip(total_lines - suffix_lines) {
        result_lines.push(line.to_string());
    }

    // Return lines and truncation info (number of lines hidden)
    let hidden_lines = total_lines - prefix_lines - suffix_lines;
    (result_lines, Some((prefix_lines, hidden_lines)))
}

/// Represents formatted output with truncation metadata
#[derive(Debug)]
struct FormattedOutput {
    head: String,
    tail: Option<String>,
    suffix_start_line: Option<usize>,
    suffix_end_line: Option<usize>,
    prefix_end_line: usize,
}

/// Represents the result of processing a stream
#[derive(Debug)]
struct ProcessedStream {
    output: FormattedOutput,
    total_lines: usize,
}

/// Helper to process a stream and return structured output
fn process_stream(content: &str, prefix_lines: usize, suffix_lines: usize) -> ProcessedStream {
    let (lines, truncation_info) = clip_by_lines(content, prefix_lines, suffix_lines);
    let total_lines = content.lines().count();
    let output = tag_output(lines, truncation_info, total_lines);

    ProcessedStream { output, total_lines }
}

/// Helper function to format potentially truncated output for stdout or stderr
fn tag_output(
    lines: Vec<String>,
    truncation_info: Option<(usize, usize)>,
    total_lines: usize,
) -> FormattedOutput {
    match truncation_info {
        Some((prefix_count, hidden_count)) => {
            let suffix_start_line = prefix_count + hidden_count + 1;
            let mut head = String::new();
            let mut tail = String::new();

            // Add prefix lines
            for line in lines.iter().take(prefix_count) {
                head.push_str(line);
                head.push('\n');
            }

            // Add suffix lines
            for line in lines.iter().skip(prefix_count) {
                tail.push_str(line);
                tail.push('\n');
            }

            FormattedOutput {
                head,
                tail: Some(tail),
                suffix_start_line: Some(suffix_start_line),
                suffix_end_line: Some(total_lines),
                prefix_end_line: prefix_count,
            }
        }
        None => {
            // No truncation, output all lines
            let mut content = String::new();
            for (i, line) in lines.iter().enumerate() {
                content.push_str(line);
                if i < lines.len() - 1 {
                    content.push('\n');
                }
            }
            FormattedOutput {
                head: content,
                tail: None,
                suffix_start_line: None,
                suffix_end_line: None,
                prefix_end_line: total_lines,
            }
        }
    }
}

/// Truncates shell output and creates a temporary file if needed
pub fn truncate_shell_output(
    stdout: &str,
    stderr: &str,
    prefix_lines: usize,
    suffix_lines: usize,
) -> TruncatedShellOutput {
    let stdout_result = process_stream(stdout, prefix_lines, suffix_lines);
    let stderr_result = process_stream(stderr, prefix_lines, suffix_lines);

    TruncatedShellOutput {
        stderr: Stderr {
            head: stderr_result.output.head,
            tail: stderr_result.output.tail,
            total_lines: stderr_result.total_lines,
            head_end_line: stderr_result.output.prefix_end_line,
            tail_start_line: stderr_result.output.suffix_start_line,
            tail_end_line: stderr_result.output.suffix_end_line,
        },
        stdout: Stdout {
            head: stdout_result.output.head,
            tail: stdout_result.output.tail,
            total_lines: stdout_result.total_lines,
            head_end_line: stdout_result.output.prefix_end_line,
            tail_start_line: stdout_result.output.suffix_start_line,
            tail_end_line: stdout_result.output.suffix_end_line,
        },
    }
}

/// Trait for stream elements that can be converted to XML elements
pub trait StreamElement {
    fn stream_name(&self) -> &'static str;
    fn head_content(&self) -> &str;
    fn tail_content(&self) -> Option<&str>;
    fn total_lines(&self) -> usize;
    fn head_end_line(&self) -> usize;
    fn tail_start_line(&self) -> Option<usize>;
    fn tail_end_line(&self) -> Option<usize>;
}

impl StreamElement for Stdout {
    fn stream_name(&self) -> &'static str {
        "stdout"
    }

    fn head_content(&self) -> &str {
        &self.head
    }

    fn tail_content(&self) -> Option<&str> {
        self.tail.as_deref()
    }

    fn total_lines(&self) -> usize {
        self.total_lines
    }

    fn head_end_line(&self) -> usize {
        self.head_end_line
    }

    fn tail_start_line(&self) -> Option<usize> {
        self.tail_start_line
    }

    fn tail_end_line(&self) -> Option<usize> {
        self.tail_end_line
    }
}

impl StreamElement for Stderr {
    fn stream_name(&self) -> &'static str {
        "stderr"
    }

    fn head_content(&self) -> &str {
        &self.head
    }

    fn tail_content(&self) -> Option<&str> {
        self.tail.as_deref()
    }

    fn total_lines(&self) -> usize {
        self.total_lines
    }

    fn head_end_line(&self) -> usize {
        self.head_end_line
    }

    fn tail_start_line(&self) -> Option<usize> {
        self.tail_start_line
    }

    fn tail_end_line(&self) -> Option<usize> {
        self.tail_end_line
    }
}
pub struct Stdout {
    pub head: String,
    pub tail: Option<String>,
    pub total_lines: usize,
    pub head_end_line: usize,
    pub tail_start_line: Option<usize>,
    pub tail_end_line: Option<usize>,
}

pub struct Stderr {
    pub head: String,
    pub tail: Option<String>,
    pub total_lines: usize,
    pub head_end_line: usize,
    pub tail_start_line: Option<usize>,
    pub tail_end_line: Option<usize>,
}

/// Result of shell output truncation
pub struct TruncatedShellOutput {
    pub stdout: Stdout,
    pub stderr: Stderr,
}

/// Represents the result of fetch content truncation
#[derive(Debug)]
pub struct TruncatedFetchOutput {
    pub content: String,
}

/// Truncates fetch content based on character limit
pub fn truncate_fetch_content(content: &str, truncation_limit: usize) -> TruncatedFetchOutput {
    let original_length = content.len();
    let is_truncated = original_length > truncation_limit;

    let truncated_content = if is_truncated {
        content.chars().take(truncation_limit).collect()
    } else {
        content.to_string()
    };

    TruncatedFetchOutput { content: truncated_content }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TruncatedContent {
    Line(Vec<String>),
    Byte(Vec<Vec<u8>>),
    Full(Vec<String>),
}

impl From<Vec<String>> for TruncatedContent {
    fn from(value: Vec<String>) -> Self {
        TruncatedContent::Full(value)
    }
}

/// Represents the result of truncation
#[derive(Debug, Clone, PartialEq, Eq, Setters)]
pub struct TruncatedOutput {
    pub content: TruncatedContent,
    pub total: usize,
    pub start: usize,
    pub end: usize,
}

impl TruncatedOutput {
    pub fn from_lines(lines: Vec<String>) -> Self {
        TruncatedOutput {
            total: lines.len(),
            end: lines.len(),
            content: TruncatedContent::Line(lines),
            start: 0,
        }
    }

    #[cfg(test)]
    pub fn from_bytes(bytes: Vec<Vec<u8>>) -> Self {
        TruncatedOutput {
            total: bytes.len(),
            end: bytes.len(),
            content: TruncatedContent::Byte(bytes),
            start: 0,
        }
    }

    pub fn truncate_items(mut self, start: usize, max_items: usize) -> Self {
        match &self.content {
            TruncatedContent::Full(content) | TruncatedContent::Line(content) => {
                let total_items = content.len();
                let is_truncated = total_items > max_items;
                let truncated = if is_truncated {
                    content
                        .into_iter()
                        .skip(start)
                        .take(max_items)
                        .cloned()
                        .collect::<Vec<_>>()
                } else {
                    content.clone()
                };

                if is_truncated {
                    self.start = start;
                    self.end = start.saturating_add(truncated.len());
                    self.content = TruncatedContent::Line(truncated);
                }
            }
            TruncatedContent::Byte(content) => {
                let total_items = content.len();
                let is_truncated = total_items > max_items;
                let truncated = if is_truncated {
                    content
                        .into_iter()
                        .skip(start)
                        .take(max_items)
                        .cloned()
                        .collect::<Vec<_>>()
                } else {
                    content.clone()
                };

                if is_truncated {
                    self.start = start;
                    self.end = start.saturating_add(truncated.len());
                    self.content = TruncatedContent::Line(
                        truncated
                            .into_iter()
                            .map(|vec| String::from_utf8_lossy(&vec).to_string())
                            .collect(),
                    );
                }
            }
        }
        self
    }
    
    pub fn truncate_bytes(mut self, max_bytes: usize) -> Self {
        match &self.content {
           TruncatedContent::Full(content) | TruncatedContent::Line(content) => {
                let original_size = content.len();
                let mut total_bytes = 0;
                let mut truncated = Vec::with_capacity(original_size);
                for item in content {
                    let current_bytes = item.as_bytes();
                    total_bytes += current_bytes.len();
                    if total_bytes >= max_bytes {
                        break;
                    }
                    truncated.push(current_bytes.to_vec());
                }

                if original_size != truncated.len() {
                    self.end = self.start + truncated.len();
                    self.content = TruncatedContent::Byte(truncated);
                }
            }
            TruncatedContent::Byte(content) => {
                let original_size = content.len();
                let mut total_bytes = 0;
                let mut truncated = Vec::with_capacity(original_size);
                for item in content {
                    total_bytes += item.len();
                    if total_bytes >= max_bytes {
                        break;
                    }
                    truncated.push(item.clone());
                }
                if original_size != truncated.len() {
                    self.end = self.start + truncated.len();
                    self.content = TruncatedContent::Byte(truncated);
                }
            }
        }
        self
    }
}

/// Truncates search output based on line limit, using search directory for
/// relative paths
pub fn truncate_search_output(
    output: &[Match],
    start_line: usize,
    max_lines: usize,
    max_bytes: usize,
    search_dir: &Path,
) -> TruncatedOutput {
    let output = output
        .iter()
        .map(|v| format_match(v, search_dir))
        .collect::<Vec<_>>();

    // Apply truncation strategies
    TruncatedOutput::from_lines(output)
        .truncate_items(start_line, max_lines)
        .truncate_bytes(max_bytes)
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_line_based_truncation() {
        let data = vec![
            "line 1".to_string(),
            "line 2".to_string(),
            "line 3".to_string(),
            "line 4".to_string(),
            "line 5".to_string(),
        ];

        let actual = TruncatedOutput::from_lines(data.clone()).truncate_items(1, 3);
        let expected =
            TruncatedOutput::from_lines(data.into_iter().skip(1).take(3).collect::<Vec<_>>())
                .start(1)
                .end(4)
                .total(5);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_bytes_based_truncation() {
        // total entries = 5
        // each entry 5 bytes long
        // total size = 25 bytes
        let data = vec![
            "A".repeat(5).into_bytes(),
            "B".repeat(5).into_bytes(),
            "C".repeat(5).into_bytes(),
            "D".repeat(5).into_bytes(),
            "E".repeat(5).into_bytes(),
        ];
        let actual = TruncatedOutput::from_bytes(data.clone()).truncate_bytes(20);
        let expected = TruncatedOutput::from_bytes(data.into_iter().take(3).collect::<Vec<_>>())
            .end(3)
            .total(5);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_both_truncation_strategies() {
        let data = vec![
            "A".repeat(900),
            "B".repeat(10),
            "C".repeat(25),
            "D".repeat(35),
            "E".repeat(45),
        ];
        let actual = TruncatedOutput::from_lines(data.clone())
            .truncate_items(0, 10)
            .truncate_bytes(925);

        let expected = TruncatedOutput::from_bytes(
            data.into_iter()
                .map(|s| s.into_bytes())
                .take(2)
                .collect::<Vec<_>>(),
        )
        .end(2)
        .total(5);

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_both_truncation_strategies_with_lower_byte_limit() {
        let data = vec![
            "A".repeat(900),
            "B".repeat(10),
            "C".repeat(25),
            "D".repeat(35),
            "E".repeat(45),
        ];
        let actual = TruncatedOutput::from_lines(data.clone())
            .truncate_items(0, 10)
            .truncate_bytes(120);
        let expected = TruncatedOutput::from_bytes(vec![]).total(5);
        assert_eq!(actual, expected);
    }
}
