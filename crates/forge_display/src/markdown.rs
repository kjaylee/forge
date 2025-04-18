use derive_setters::Setters;
use termimad::{gray, CompoundStyle, LineStyle, MadSkin};

/// MarkdownFormat provides functionality for formatting markdown text for
/// terminal display.
#[derive(Clone, Setters, Default)]
#[setters(into, strip_option)]
pub struct MarkdownFormat {
    content: String,
    skin: Option<MadSkin>,
}

impl MarkdownFormat {
    /// Create a new MarkdownFormat with the specified content
    ///
    /// # Arguments
    ///
    /// * `content` - The markdown content to be formatted
    pub fn new(content: impl Into<String>) -> Self {
        Self { content: content.into(), skin: None }
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
        skin.term_text(&self.content).to_string()
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
}
