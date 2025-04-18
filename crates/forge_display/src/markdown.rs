use derive_setters::Setters;
use regex::Regex;
use termimad::{gray, CompoundStyle, LineStyle, MadSkin};

/// MarkdownFormat provides functionality for formatting markdown text for
/// terminal display.
#[derive(Clone, Setters, Default)]
#[setters(into, strip_option)]
pub struct MarkdownFormat {
    content: String,
    skin: Option<MadSkin>,
    max_consecutive_newlines: usize,
}

impl MarkdownFormat {
    /// Create a new MarkdownFormat with the specified content
    ///
    /// # Arguments
    ///
    /// * `content` - The markdown content to be formatted
    pub fn new(content: impl Into<String>) -> Self {
        Self {
            content: content.into(),
            skin: None,
            max_consecutive_newlines: 2,
        }
    }

    /// Render the markdown content to a string formatted for terminal display.
    ///
    /// This method applies the specified skin (or default if none)
    /// to format the markdown content for terminal output.
    pub fn format(&self) -> String {
        let mut skin = MadSkin::default();
        let compound_style = CompoundStyle::new(Some(gray(17)), None, Default::default());
        skin.inline_code = compound_style.clone();
        skin.code_block = LineStyle::new(compound_style, Default::default());
        let skin = self.skin.as_ref().unwrap_or(&skin);

        // Strip excessive newlines before rendering
        let processed_content = self.strip_excessive_newlines(&self.content);

        skin.term_text(&processed_content).to_string()
    }

    /// Strip excessive consecutive newlines from content
    ///
    /// Reduces any sequence of more than max_consecutive_newlines to exactly
    /// max_consecutive_newlines
    fn strip_excessive_newlines(&self, content: &str) -> String {
        if content.is_empty() {
            return content.to_string();
        }

        let pattern = format!(r"\n{{{},}}", self.max_consecutive_newlines + 1);
        let re = Regex::new(&pattern).unwrap();
        let replacement = "\n".repeat(self.max_consecutive_newlines);

        re.replace_all(content, replacement.as_str()).to_string()
    }
}

/// Convenience function to quickly render markdown without creating a
/// MarkdownFormat instance
///
/// # Arguments
///
/// * `content` - The markdown content to be formatted
pub fn render(content: &str) -> String {
    MarkdownFormat::new(content.trim())
        .format()
        .trim()
        .to_string()
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_render_simple_markdown() {
        let fixture = "# Test Heading\nThis is a test.";
        let actual = render(fixture);

        // Basic verification that output is non-empty
        assert!(!actual.is_empty());
    }

    #[test]
    fn test_render_empty_markdown() {
        let fixture = "";
        let actual = render(fixture);

        // Verify empty input produces empty output
        assert!(actual.is_empty());
    }

    #[test]
    fn test_markdown_format_with_custom_skin() {
        let fixture = "**Bold text** and *italic text*";
        let mut skin = MadSkin::default();
        skin.bold.set_fg(termimad::rgb(255, 0, 0)); // Red bold text

        let actual = MarkdownFormat::new(fixture).skin(skin).format();

        // Verify output contains ANSI color codes (we can't check exact contents due to
        // styling)
        assert!(!actual.is_empty());
    }

    #[test]
    fn test_strip_excessive_newlines_default() {
        let fixture = "Line 1\n\n\n\nLine 2";
        let formatter = MarkdownFormat::new(fixture);
        let actual = formatter.strip_excessive_newlines(fixture);
        let expected = "Line 1\n\nLine 2";

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_strip_excessive_newlines_custom() {
        let fixture = "Line 1\n\n\n\nLine 2";
        let formatter = MarkdownFormat::new(fixture).max_consecutive_newlines(3_usize);
        let actual = formatter.strip_excessive_newlines(fixture);
        let expected = "Line 1\n\n\nLine 2";

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_format_with_excessive_newlines() {
        let fixture = "# Heading\n\n\n\nParagraph";

        // Use the default max_consecutive_newlines (2)
        let actual = MarkdownFormat::new(fixture).format();

        // Compare with expected content containing only 2 newlines
        let expected = MarkdownFormat::new("# Heading\n\nParagraph").format();

        // Strip any ANSI codes and whitespace for comparison
        let actual_clean = strip_ansi_escapes::strip_str(&actual).trim().to_string();
        let expected_clean = strip_ansi_escapes::strip_str(&expected).trim().to_string();

        assert_eq!(actual_clean, expected_clean);
    }

    #[test]
    fn test_format_with_custom_max_newlines() {
        let fixture = "# Heading\n\n\n\nParagraph";

        // Use a custom max_consecutive_newlines (1)
        let actual = MarkdownFormat::new(fixture)
            .max_consecutive_newlines(1_usize)
            .format();

        // Compare with expected content containing only 1 newline
        let expected = MarkdownFormat::new("# Heading\nParagraph").format();

        // Strip any ANSI codes and whitespace for comparison
        let actual_clean = strip_ansi_escapes::strip_str(&actual).trim().to_string();
        let expected_clean = strip_ansi_escapes::strip_str(&expected).trim().to_string();

        assert_eq!(actual_clean, expected_clean);
    }
}
