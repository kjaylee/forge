use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

/// Represents a range of lines in a file or content
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineRange {
    pub start: usize,
    pub end: usize,
    pub total_lines: usize,
}

/// Information about a temporary file used to store large content
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TempFileInfo {
    pub path: String,
    pub original_source: String, // e.g., "shell output", "file content"
}

/// Metadata about a range displayed from a larger content
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeMetadata {
    pub displayed_range_start: usize,
    pub displayed_range_end: usize,
    pub total_lines: usize,
    pub temp_file_path: Option<String>,
}

/// Constants for range handling
pub const DEFAULT_LINE_LIMIT: usize = 1000;

/// Counts the number of lines in a string
pub fn count_lines(content: &str) -> usize {
    content.lines().count()
}

/// Extracts a specific line range from content
pub fn extract_line_range(content: &str, start: usize, end: usize) -> Result<String> {
    let total_lines = count_lines(content);

    // Handle out of bounds
    if start > total_lines {
        return Err(anyhow::anyhow!(
            "Start line {} exceeds total lines {}",
            start,
            total_lines
        ));
    }

    // Clamp end to total_lines if needed
    let end = std::cmp::min(end, total_lines);

    // Extract the selected range
    let result = content
        .lines()
        .skip(start.saturating_sub(1)) // Convert to 0-based indexing
        .take(end.saturating_sub(start).saturating_add(1))
        .collect::<Vec<&str>>()
        .join("\n");

    Ok(result)
}

/// Generates a temporary file path with a given prefix
fn generate_temp_file_path(prefix: &str) -> String {
    let timestamp = chrono::Utc::now().format("%Y%m%d_%H%M%S").to_string();
    let random = rand::random::<u16>();
    let temp_dir = std::env::temp_dir();

    format!(
        "{}/{}_{:04x}_{}",
        temp_dir.to_string_lossy(),
        prefix,
        random,
        timestamp
    )
}

/// Writes content to a temporary file and returns the file info
pub fn write_to_temp_file(content: &str, prefix: &str) -> Result<TempFileInfo> {
    let path = generate_temp_file_path(prefix);
    std::fs::write(&path, content)
        .with_context(|| format!("Failed to write temporary file {}", path))?;

    Ok(TempFileInfo { path, original_source: prefix.to_string() })
}

/// Determines appropriate line ranges for displaying large content
pub fn determine_display_range(
    total_lines: usize,
    requested_start: Option<usize>,
    requested_end: Option<usize>,
) -> (usize, usize) {
    // If content is smaller than the limit, show all of it
    if total_lines <= DEFAULT_LINE_LIMIT {
        return (1, total_lines);
    }

    // If specific range requested, honor it
    if let (Some(start), Some(end)) = (requested_start, requested_end) {
        return (start, end);
    }

    // If only start specified, show DEFAULT_LINE_LIMIT lines from there
    if let Some(start) = requested_start {
        let end = std::cmp::min(start + DEFAULT_LINE_LIMIT - 1, total_lines);
        return (start, end);
    }

    // If only end specified, show DEFAULT_LINE_LIMIT lines up to there
    if let Some(end) = requested_end {
        let start = end.saturating_sub(DEFAULT_LINE_LIMIT).saturating_add(1);
        (start, end)
    } else {
        // Show the beginning by default
        (1, DEFAULT_LINE_LIMIT)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_count_lines() {
        let fixture = "Line 1\nLine 2\nLine 3";
        let actual = count_lines(fixture);
        let expected = 3;
        assert_eq!(actual, expected);

        let fixture = "";
        let actual = count_lines(fixture);
        let expected = 0;
        assert_eq!(actual, expected);

        let fixture = "Single line";
        let actual = count_lines(fixture);
        let expected = 1;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_extract_line_range() {
        let fixture = "Line 1\nLine 2\nLine 3\nLine 4\nLine 5";

        let actual = extract_line_range(fixture, 2, 4).unwrap();
        let expected = "Line 2\nLine 3\nLine 4";
        assert_eq!(actual, expected);

        let actual = extract_line_range(fixture, 1, 2).unwrap();
        let expected = "Line 1\nLine 2";
        assert_eq!(actual, expected);

        let actual = extract_line_range(fixture, 4, 10).unwrap();
        let expected = "Line 4\nLine 5";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_extract_line_range_error() {
        let fixture = "Line 1\nLine 2\nLine 3";
        let result = extract_line_range(fixture, 10, 20);
        assert!(result.is_err());
    }

    #[test]
    fn test_generate_temp_file_path() {
        let actual = generate_temp_file_path("test");
        assert!(actual.contains("test_"));
    }

    #[test]
    fn test_determine_display_range() {
        // Small file, show everything
        let (start, end) = determine_display_range(500, None, None);
        assert_eq!((start, end), (1, 500));

        // Large file, no range specified - show only first chunk
        let (start, end) = determine_display_range(5000, None, None);
        assert_eq!((start, end), (1, DEFAULT_LINE_LIMIT));

        // Large file with specific range
        let (start, end) = determine_display_range(5000, Some(2000), Some(3000));
        assert_eq!((start, end), (2000, 3000));

        // Large file with only start specified
        let (start, end) = determine_display_range(5000, Some(4001), None);
        assert_eq!((start, end), (4001, 5000));

        // Large file with only end specified
        let (start, end) = determine_display_range(5000, None, Some(4500));
        assert_eq!((start, end), (3501, 4500));
    }
}
