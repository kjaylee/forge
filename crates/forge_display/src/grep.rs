use std::collections::BTreeMap;

use console::style;
use regex::Regex;

/// RipGrepFormatter formats search results in ripgrep-like style.
pub struct GrepFormat(Vec<String>);

/// Represents a parsed line from grep-like output format
/// (path:line_num:content)
#[derive(Debug)]
struct ParsedLine<'a> {
    /// File path where the match was found
    path: &'a str,
    /// Line number of the match
    line_num: &'a str,
    /// Content of the matching line
    content: &'a str,
}

impl<'a> ParsedLine<'a> {
    /// Parse a line in the format "path:line_num:content"
    ///
    /// # Arguments
    /// * `line` - The line to parse in the format "path:line_num:content"
    ///
    /// # Returns
    /// * `Some(ParsedLine)` if the line matches the expected format
    /// * `None` if the line is malformed
    pub fn parse(line: &'a str) -> Option<Self> {
        let parts: Vec<_> = line.split(':').collect();
        if parts.len() != 3 {
            return None;
        }

        // Validate that path and line number parts are not empty
        // and that line number contains only digits
        if parts[0].is_empty()
            || parts[1].is_empty()
            || !parts[1].chars().all(|c| c.is_ascii_digit())
        {
            return None;
        }

        Some(Self { path: parts[0], line_num: parts[1], content: parts[2] })
    }
}

impl GrepFormat {
    pub fn new(lines: Vec<String>) -> Self {
        Self(lines)
    }

    /// Collect file entries and determine the maximum line number width
    fn collect_entries(lines: &[String]) -> (BTreeMap<&str, Vec<(&str, &str)>>, usize) {
        lines
            .iter()
            .map(String::as_str)
            .filter_map(ParsedLine::parse)
            .fold((BTreeMap::new(), 0), |(mut entries, max_width), parsed| {
                let new_width = max_width.max(parsed.line_num.len());
                entries
                    .entry(parsed.path)
                    .or_default()
                    .push((parsed.line_num, parsed.content));
                (entries, new_width)
            })
    }

    /// Format a single line with colorization and consistent padding
    fn format_line(num: &str, content: &str, regex: &Regex, padding: usize) -> String {
        // Format the line number with both left and right padding
        let line_prefix = format!("{:>padding$}:", num, padding = padding);
        let padded_prefix = format!("{} ", line_prefix);
        let styled_prefix = style(padded_prefix).dim().to_string();

        // Format the content with highlighting
        let styled_content = regex.find(content).map_or_else(
            || content.to_string(),
            |mat| {
                format!(
                    "{}{}{}",
                    &content[..mat.start()],
                    style(&content[mat.start()..mat.end()]).yellow().bold(),
                    &content[mat.end()..]
                )
            },
        );

        // Add 4 spaces between colon and content
        format!("{}    {}\n", styled_prefix, styled_content)
    }

    /// Format a group of lines for a single file
    fn format_file_group(
        path: &str,
        group: Vec<(&str, &str)>,
        regex: &Regex,
        max_num_width: usize,
    ) -> String {
        let file_header = style(path).cyan().to_string();
        let formatted_lines = group
            .into_iter()
            .map(|(num, content)| Self::format_line(num, content, regex, max_num_width))
            .collect::<String>();
        format!("{}\n{}", file_header, formatted_lines)
    }

    /// Format search results with colorized output grouped by path
    pub fn format(&self, regex: &Regex) -> String {
        if self.0.is_empty() {
            return String::new();
        }

        // First pass: collect entries and find max width
        let (entries, max_num_width) = Self::collect_entries(&self.0);

        // Print the results on separate lines
        let formatted_entries: Vec<_> = entries
            .into_iter()
            .map(|(path, group)| Self::format_file_group(path, group, regex, max_num_width))
            .collect();

        // Join all results with newlines
        formatted_entries.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_ripgrep_formatter_single_file() {
        let input = vec!["file.txt:1:first match", "file.txt:2:second match"]
            .into_iter()
            .map(String::from)
            .collect();

        let formatter = GrepFormat(input);
        let result = formatter.format(&Regex::new("match").unwrap());
        let actual = strip_ansi_escapes::strip_str(&result);
        let expected = "file.txt\n    1:    first match\n    2:    second match\n";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_ripgrep_formatter_multiple_files() {
        let input = vec![
            "file1.txt:1:match in file1",
            "file2.txt:1:first match in file2",
            "file2.txt:2:second match in file2",
            "file3.txt:1:match in file3",
        ]
        .into_iter()
        .map(String::from)
        .collect();

        let formatter = GrepFormat(input);
        let result = formatter.format(&Regex::new("file").unwrap());
        let actual = strip_ansi_escapes::strip_str(&result);

        let expected = "file1.txt\n    1:    match in file1\n\nfile2.txt\n    1:    first match in file2\n    2:    second match in file2\n\nfile3.txt\n    1:    match in file3\n";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_ripgrep_formatter_empty_input() {
        let formatter = GrepFormat(vec![]);
        let result = formatter.format(&Regex::new("file").unwrap());
        assert_eq!(result, "");
    }

    #[test]
    fn test_ripgrep_formatter_line_number_padding() {
        let input = vec![
            "file.txt:1:first line",
            "file.txt:5:fifth line",
            "file.txt:10:tenth line",
            "file.txt:100:hundredth line",
        ]
        .into_iter()
        .map(String::from)
        .collect();

        let formatter = GrepFormat(input);
        let result = formatter.format(&Regex::new("line").unwrap());
        let actual = strip_ansi_escapes::strip_str(&result);

        // Verify that all line numbers are right-aligned to the same width
        let expected = "file.txt\n      1:    first line\n      5:    fifth line\n     10:    tenth line\n    100:    hundredth line\n";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_parsed_line_valid_input() {
        let line = "path/to/file.txt:123:some content";
        let parsed = ParsedLine::parse(line).unwrap();
        assert_eq!(parsed.path, "path/to/file.txt");
        assert_eq!(parsed.line_num, "123");
        assert_eq!(parsed.content, "some content");
    }

    #[test]
    fn test_parsed_line_invalid_input() {
        assert!(ParsedLine::parse("invalid").is_none());
        assert!(ParsedLine::parse("only:one:separator").is_none());
        assert!(ParsedLine::parse("too:many:separators:here").is_none());
    }

    #[test]
    fn test_ripgrep_formatter_malformed_input() {
        let input = vec![
            "file.txt:1:valid match",
            "malformed line without separator",
            "file.txt:2:another valid match",
        ]
        .into_iter()
        .map(String::from)
        .collect();

        let formatter = GrepFormat(input);
        let result = formatter.format(&Regex::new("match").unwrap());
        let actual = strip_ansi_escapes::strip_str(&result);

        let expected = "file.txt\n    1:    valid match\n    2:    another valid match\n";
        assert_eq!(actual, expected);
    }
}
