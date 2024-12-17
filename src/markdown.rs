#![allow(dead_code)]
use pulldown_cmark::{Event, Parser, Tag};
use std::io::{self, Write};
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

    pub fn render_chunk(&mut self, chunk: &str, end_md: bool) -> io::Result<()> {
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
            self.render(&self.buffer)?;
            self.buffer.clear();
        }

        Ok(())
    }

    pub fn render(&self, markdown: &str) -> io::Result<()> {
        let parser = Parser::new(markdown);
        let mut in_code_block = false;
        let mut code_buffer = String::new();
        let mut text_buffer = String::new();
        let theme = &self.theme_set.themes["base16-ocean.dark"];
        let stdout = io::stdout();
        let mut writer = stdout.lock();

        for event in parser {
            match event {
                Event::Start(Tag::CodeBlock(_)) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    in_code_block = true;
                    writeln!(writer, "\x1b[38;5;244m{}\x1b[0m", "─".repeat(80))?;
                }
                Event::End(Tag::CodeBlock(_)) => {
                    in_code_block = false;
                    if let Some(syntax) = self.syntax_set.find_syntax_by_extension("rs") {
                        let mut highlighter = syntect::easy::HighlightLines::new(syntax, theme);
                        let lines: Vec<&str> = code_buffer.lines().collect();
                        let num_width = lines.len().to_string().len();

                        for (i, line) in lines.iter().enumerate() {
                            write!(
                                writer,
                                "\x1b[38;5;244m{:>width$} │ \x1b[0m",
                                i + 1,
                                width = num_width
                            )?;
                            let ranges: Vec<(Style, &str)> =
                                highlighter.highlight_line(line, &self.syntax_set).unwrap();
                            let escaped =
                                syntect::util::as_24_bit_terminal_escaped(&ranges[..], false);
                            write!(writer, "{}", escaped)?;
                            writeln!(writer)?;
                        }
                        writeln!(writer, "\x1b[38;5;244m{}\x1b[0m", "─".repeat(80))?;
                        write!(writer, "\x1b[0m")?;
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
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::End(Tag::Paragraph) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::Heading(level, ..)) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push('\n');
                    text_buffer.push_str(&"#".repeat(level as usize));
                    text_buffer.push(' ');
                }
                Event::End(Tag::Heading(..)) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::BlockQuote) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str("> ");
                }
                Event::End(Tag::BlockQuote) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::List(Some(num))) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str(&format!("{}. ", num));
                }
                Event::Start(Tag::List(None)) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str("- ");
                }
                Event::End(Tag::List(_)) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::Start(Tag::Item) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                }
                Event::End(Tag::Item) => {
                    if !text_buffer.is_empty() {
                        self.skin.print_text(&text_buffer);
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
                        self.skin.print_text(&text_buffer);
                        text_buffer.clear();
                    }
                    text_buffer.push_str("\n---\n");
                }
                _ => {}
            }
        }

        // Render any remaining text
        if !text_buffer.is_empty() {
            self.skin.print_text(&text_buffer);
        }

        writer.flush()
    }

    pub fn set_skin_colors(
        &mut self,
        header: (u8, u8, u8),
        bold: (u8, u8, u8),
        italic: (u8, u8, u8),
        paragraph: (u8, u8, u8),
    ) {
        self.skin.set_headers_fg(rgb(header.0, header.1, header.2));
        self.skin.bold.set_fg(rgb(bold.0, bold.1, bold.2));
        self.skin.italic.set_fg(rgb(italic.0, italic.1, italic.2));
        self.skin
            .paragraph
            .set_fg(rgb(paragraph.0, paragraph.1, paragraph.2));
    }
}
