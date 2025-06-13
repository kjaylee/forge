use std::path::PathBuf;

use forge_domain::Environment;
use forge_template::Element;

use crate::utils::format_match;
use crate::{FsCreateService, Match, Services};

pub async fn create_temp_file<S: Services>(
    services: &S,
    prefix: &str,
    ext: &str,
    content: &str,
) -> anyhow::Result<PathBuf> {
    let path = tempfile::Builder::new()
        .keep(true)
        .prefix(prefix)
        .suffix(ext)
        .tempfile()?
        .into_temp_path()
        .to_path_buf();
    services
        .fs_create_service()
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

/// Helper to process a stream and return (formatted_output, is_truncated)
fn process_stream(
    content: &str,
    tag: &str,
    prefix_lines: usize,
    suffix_lines: usize,
) -> (Element, bool) {
    let (lines, truncation_info) = clip_by_lines(content, prefix_lines, suffix_lines);
    let is_truncated = truncation_info.is_some();
    let total_lines = content.lines().count();
    let output = tag_output(lines, truncation_info, tag, total_lines);

    (output, is_truncated)
}

/// Helper function to format potentially truncated output for stdout or stderr
fn tag_output(
    lines: Vec<String>,
    truncation_info: Option<(usize, usize)>,
    tag: &str,
    total_lines: usize,
) -> Element {
    match truncation_info {
        Some((prefix_count, hidden_count)) => {
            let suffix_start_line = prefix_count + hidden_count + 1;

            let mut output = String::new();

            // Add prefix lines
            for line in lines.iter().take(prefix_count) {
                output.push_str(line);
                output.push('\n');
            }

            // Add truncation marker
            output.push_str(&format!("... [{hidden_count} lines omitted] ...\n"));

            // Add suffix lines
            for line in lines.iter().skip(prefix_count) {
                output.push_str(line);
                output.push('\n');
            }

            Element::new(tag)
                .append(Element::new("truncated").text("true"))
                .append(Element::new("displayed_lines").text(prefix_count))
                .append(Element::new("total_lines").text(total_lines))
                .append(create_truncation_info(
                    prefix_count,
                    total_lines - suffix_start_line,
                    hidden_count,
                ))
                .append(Element::new("content").cdata(output))
        }
        None => {
            // No truncation, output all lines
            let mut output = String::new();
            for (i, line) in lines.iter().enumerate() {
                output.push_str(line);
                if i < lines.len() - 1 {
                    output.push('\n');
                }
            }
            Element::new(tag)
                .append(Element::new("truncated").text("false"))
                .append(Element::new("total_lines").text(total_lines))
                .append(create_truncation_info(output.len(), 0, 0))
                .append(Element::new("content").cdata(output))
        }
    }
}

fn create_truncation_info(
    prefix_count: usize,
    suffix_count: usize,
    hidden_count: usize,
) -> Element {
    Element::new("truncation_info")
        .append(Element::new("head_lines").text(prefix_count))
        .append(Element::new("tail_lines").text(suffix_count))
        .append(Element::new("omitted_lines").text(hidden_count))
}

/// Truncates shell output and creates a temporary file if needed
pub fn truncate_shell_output(
    stdout: &str,
    stderr: &str,
    prefix_lines: usize,
    suffix_lines: usize,
) -> TruncatedShellOutput {
    let (stdout_output, stdout_truncated) =
        process_stream(stdout, "stdout", prefix_lines, suffix_lines);
    let (stderr_output, stderr_truncated) =
        process_stream(stderr, "stderr", prefix_lines, suffix_lines);

    TruncatedShellOutput {
        stdout: stdout_output,
        stderr: stderr_output,
        stdout_truncated,
        stderr_truncated,
    }
}

/// Result of shell output truncation
pub struct TruncatedShellOutput {
    pub stdout: Element,
    pub stderr: Element,
    pub stdout_truncated: bool,
    pub stderr_truncated: bool,
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

/// Represents the result of fs_search truncation
#[derive(Debug)]
pub struct TruncatedSearchOutput {
    pub output: String,
    pub total_lines: u64,
    pub start_line: u64,
    pub end_line: u64,
}

/// Truncates search output based on line limit
pub fn truncate_search_output(
    output: &[Match],
    start_line: u64,
    count: u64,
    env: &Environment,
) -> TruncatedSearchOutput {
    let total_outputs = output.len() as u64;
    let is_truncated = total_outputs > count;
    let output = output
        .iter()
        .map(|v| format_match(v, env))
        .collect::<Vec<_>>();

    let truncated_output = if is_truncated {
        output
            .iter()
            .skip(start_line as usize)
            .take(count as usize)
            .map(String::from)
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        output.join("\n")
    };

    TruncatedSearchOutput {
        output: truncated_output,
        total_lines: total_outputs,
        start_line,
        end_line: if is_truncated {
            start_line + count
        } else {
            total_outputs
        },
    }
}
