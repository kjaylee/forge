#![allow(dead_code)]
use std::io::Write;

use pulldown_cmark::{Event, Parser, Tag};
use syntect::highlighting::{Style, ThemeSet};
use syntect::parsing::SyntaxSet;
use termimad::{rgb, MadSkin};

const BUFFER_CAPACITY: usize = 512;

pub struct MarkdownRenderer {
    syntax_set: SyntaxSet,
    theme_set: ThemeSet,
    skin: MadSkin,
    buffer: String,
}

impl Default for MarkdownRenderer {
    fn default() -> Self {
        let mut skin = MadSkin::default();
        skin.set_headers_fg(rgb(255, 187, 0));
        skin.bold.set_fg(rgb(255, 215, 0));
        skin.italic.set_fg(rgb(215, 255, 135));
        skin.paragraph.set_fg(rgb(220, 220, 220));

        Self {
            syntax_set: SyntaxSet::load_defaults_newlines(),
            theme_set: ThemeSet::load_defaults(),
            skin,
            buffer: String::with_capacity(BUFFER_CAPACITY),
        }
    }
}

impl MarkdownRenderer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn render_chunk(&mut self, chunk: &str, end_md: bool) -> std::io::Result<()> {
        self.buffer.push_str(chunk);

        let should_render = if end_md {
            true
        } else {
            // Count occurrences of code block markers
            let code_block_count = self.buffer.matches("```").count();

            if code_block_count == 0 {
                self.buffer.len() >= BUFFER_CAPACITY
            } else {
                // If we have an even number of markers and at least 2, we have complete code blocks
                code_block_count % 2 == 0
            }
        };

        if should_render {
            let rendered = self.render(&self.buffer)?;
            //TODO: move this writer logic to separate module, create runtime that can support this op.
            let stdout = std::io::stdout();
            let mut writer = stdout.lock();
            writer.write(rendered.as_bytes())?;
            self.buffer.clear();
        }

        Ok(())
    }

    fn render(&self, markdown: &str) -> std::io::Result<String> {
        let parser = Parser::new(markdown);
        let mut in_code_block = false;
        let mut code_buffer = String::new();
        let mut text_buffer = String::new();
        let mut output = String::new();
        let theme = &self.theme_set.themes["base16-ocean.dark"];

        for event in parser {
            match event {
                Event::Start(Tag::CodeBlock(_)) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    in_code_block = true;
                    output.push_str(&format!("\x1b[38;5;244m{}\x1b[0m\n", "─".repeat(80)));
                }
                Event::End(Tag::CodeBlock(_)) => {
                    in_code_block = false;
                    if let Some(syntax) = self.syntax_set.find_syntax_by_extension("rs") {
                        let mut highlighter = syntect::easy::HighlightLines::new(syntax, theme);
                        let lines: Vec<&str> = code_buffer.lines().collect();
                        let num_width = lines.len().to_string().len();

                        for (i, line) in lines.iter().enumerate() {
                            output.push_str(&format!(
                                "\x1b[38;5;244m{:>width$} │ \x1b[0m",
                                i + 1,
                                width = num_width
                            ));
                            let ranges: Vec<(Style, &str)> =
                                highlighter.highlight_line(line, &self.syntax_set).unwrap();
                            let escaped =
                                syntect::util::as_24_bit_terminal_escaped(&ranges[..], false);
                            output.push_str(&escaped);
                            output.push('\n');
                        }
                        output.push_str(&format!("\x1b[38;5;244m{}\x1b[0m\n", "─".repeat(80)));
                        output.push_str("\x1b[0m");
                    }
                    code_buffer.clear();
                }
                Event::Text(text) => {
                    if in_code_block {
                        code_buffer.push_str(&text);
                    } else {
                        text_buffer.push_str(&text);
                    }
                }
                Event::Start(Tag::Paragraph) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::End(Tag::Paragraph) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::Heading(level, ..)) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push('\n');
                    text_buffer.push_str(&"#".repeat(level as usize));
                    text_buffer.push(' ');
                }
                Event::End(Tag::Heading(..)) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    output.push('\n');
                }
                Event::Start(Tag::BlockQuote) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str("> ");
                }
                Event::End(Tag::BlockQuote) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::List(Some(num))) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str(&format!("{}. ", num));
                }
                Event::Start(Tag::List(None)) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str("- ");
                }
                Event::End(Tag::List(_)) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::Item) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::End(Tag::Item) => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::Link(_link_type, _dest, _title)) => {
                    text_buffer.push('[');
                }
                Event::End(Tag::Link(_link_type, dest, title)) => {
                    text_buffer.push_str(&format!("]({})", dest));
                    if !title.is_empty() {
                        text_buffer.push_str(&format!(" \"{}\"", title));
                    }
                }
                Event::Start(Tag::Image(_link_type, _dest, _title)) => {
                    text_buffer.push_str("![");
                }
                Event::End(Tag::Image(_link_type, dest, title)) => {
                    text_buffer.push_str(&format!("]({})", dest));
                    if !title.is_empty() {
                        text_buffer.push_str(&format!(" \"{}\"", title));
                    }
                }
                Event::Start(Tag::Emphasis) => {
                    text_buffer.push('*');
                }
                Event::End(Tag::Emphasis) => {
                    text_buffer.push('*');
                }
                Event::Start(Tag::Strong) => {
                    text_buffer.push_str("**");
                }
                Event::End(Tag::Strong) => {
                    text_buffer.push_str("**");
                }
                Event::Code(code) => {
                    text_buffer.push('`');
                    text_buffer.push_str(&code);
                    text_buffer.push('`');
                }
                Event::Html(html) => {
                    text_buffer.push_str(&html);
                }
                Event::FootnoteReference(name) => {
                    text_buffer.push_str(&format!("[^{}]", name));
                }
                Event::SoftBreak => {
                    text_buffer.push(' ');
                }
                Event::HardBreak => {
                    text_buffer.push('\n');
                }
                Event::Rule => {
                    if !text_buffer.is_empty() {
                        output.push_str(&text_buffer);
                        text_buffer.clear();
                    }
                    output.push_str("\n---\n");
                }
                _ => {}
            }
        }

        // Render any remaining text
        if !text_buffer.is_empty() {
            output.push_str(&text_buffer);
        }

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use regex::Regex;

    fn setup() -> MarkdownRenderer {
        MarkdownRenderer::new()
    }

    /// Strips ANSI escape codes from a string
    fn strip_ansi_codes(s: &str) -> String {
        let re = Regex::new(r"\x1b\[[^m]*m").unwrap();
        re.replace_all(s, "").to_string()
    }

    #[test]
    fn test_render_plain_text() -> std::io::Result<()> {
        let renderer = setup();
        let result = renderer.render("Hello, world!")?;
        let clean_result = strip_ansi_codes(&result);
        
        insta::with_settings!({
            description => "Test rendering plain text without formatting",
            omit_expression => true
        }, {
            assert_snapshot!(clean_result);
        });
        Ok(())
    }

    #[test]
    fn test_render_code_block() -> std::io::Result<()> {
        let renderer = setup();
        let markdown = r#"```rust
fn main() {
    println!("Hello");
}
```"#;
        let result = renderer.render(markdown)?;
        let clean_result = strip_ansi_codes(&result);
        
        insta::with_settings!({
            description => "Test rendering code blocks with syntax highlighting (ANSI codes stripped)",
            omit_expression => true
        }, {
            assert_snapshot!(clean_result);
        });
        Ok(())
    }

    #[test]
    fn test_render_markdown_features() -> std::io::Result<()> {
        let renderer = setup();
        let markdown = r#"
# Heading 1
## Heading 2


This is a paragraph with *italic* and **bold** text.

> This is a blockquote

- List item 1
- List item 2

1. Ordered item 1
2. Ordered item 2

```rust
fn example() {
    println!("Code block");
}
```

Horizontal rule below:

---

[Link text](https://example.com)"#;
        
        let result = renderer.render(markdown)?;
        let clean_result = strip_ansi_codes(&result);
        
        insta::with_settings!({
            description => "Test rendering all markdown features (ANSI codes stripped)",
            omit_expression => true
        }, {
            assert_snapshot!(clean_result);
        });
        Ok(())
    }

}
