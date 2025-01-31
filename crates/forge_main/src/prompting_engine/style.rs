use nu_ansi_term::{Color, Style};

// Constants
pub const MAX_LEN: usize = 30;
const ARROW: &str = "➜";
const SHELL_NAME: &str = "FORGE";
const INDICATOR: &str = "⚡";
const MULTILINE_INDICATOR: &str = "::: ";
const LEFT_PAREN: &str = "(";
const RIGHT_PAREN: &str = ")";
const LEFT_BRACKET: &str = "[";
const RIGHT_BRACKET: &str = "]";

// bold style builder
pub fn bold_style(color: Color) -> Style {
    Style::new().bold().fg(color)
}

// outputs: `➜ FORGE ⚡ `
pub fn base_prompt_indicator() -> String {
    format!(
        "{} {}",
        bold_style(Color::LightGreen).paint(ARROW),
        bold_style(Color::Cyan).paint(SHELL_NAME)
    )
}

// outputs: `(title)`
pub fn format_title(title: &str) -> String {
    format!(
        "{}{}{}",
        bold_style(Color::Blue).paint(LEFT_PAREN),
        bold_style(Color::Red).paint(title),
        bold_style(Color::Blue).paint(RIGHT_PAREN)
    )
}

// outputs: `[end]`
pub fn format_end(end: &str) -> String {
    format!(
        " {}{}{}",
        bold_style(Color::DarkGray).paint(LEFT_BRACKET),
        bold_style(Color::DarkGray).paint(end),
        bold_style(Color::DarkGray).paint(RIGHT_BRACKET)
    )
}

// outputs: ` ⚡ `
pub fn format_indicator() -> String {
    format!(" {} ", bold_style(Color::LightYellow).paint(INDICATOR))
}

// outputs: `::: `
pub fn get_multiline_indicator() -> &'static str {
    MULTILINE_INDICATOR
}
