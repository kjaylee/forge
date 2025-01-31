use std::borrow::Cow;

use derive_setters::Setters;
use nu_ansi_term::{Color, Style};
use reedline::{Prompt, PromptHistorySearchStatus};

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
fn bold_style(color: Color) -> Style {
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

/// Very Specialized Prompt for the Agent Chat
#[derive(Clone, Default, Setters)]
pub struct AgentChatPrompt {
    start: Option<String>,
    end: Option<String>,
}

impl Prompt for AgentChatPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        if let Some(title) = self.start.as_ref() {
            let truncated = if title.chars().count() > MAX_LEN {
                format!(
                    "{}{}",
                    title.chars().take(MAX_LEN).collect::<String>(),
                    "..."
                )
            } else {
                title.to_string()
            };

            Cow::Owned(format!(
                "{} {}",
                base_prompt_indicator(),
                format_title(&truncated)
            ))
        } else {
            Cow::Owned(base_prompt_indicator())
        }
    }

    fn render_prompt_right(&self) -> Cow<str> {
        if let Some(end) = self.end.as_ref() {
            Cow::Owned(format_end(end))
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_indicator(&self, _prompt_mode: reedline::PromptEditMode) -> Cow<str> {
        Cow::Owned(format_indicator())
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed(get_multiline_indicator())
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: reedline::PromptHistorySearch,
    ) -> Cow<str> {
        let prefix = match history_search.status {
            PromptHistorySearchStatus::Passing => "",
            PromptHistorySearchStatus::Failing => "failing ",
        };
        Cow::Owned(format!(
            " ({}reverse-search: {}) ",
            prefix, history_search.term
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_prompt_left_with_title() {
        let prompt = AgentChatPrompt::default().start(Some("test-title".to_string()));
        let actual = prompt.render_prompt_left();
        let expected = format!("{} {}", base_prompt_indicator(), format_title("test-title"));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_without_title() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_left();
        let expected = base_prompt_indicator();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_with_long_title() {
        let long_title = "a".repeat(MAX_LEN + 10);
        let prompt = AgentChatPrompt::default().start(Some(long_title.clone()));
        let actual = prompt.render_prompt_left();
        let truncated = format!("{}{}", "a".repeat(MAX_LEN), "...");
        let expected = format!("{} {}", base_prompt_indicator(), format_title(&truncated));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_right_with_end() {
        let prompt = AgentChatPrompt::default().end(Some("test-end".to_string()));
        let actual = prompt.render_prompt_right();
        let expected = format_end("test-end");
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_right_without_end() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_right();
        let expected = "";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_indicator() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_indicator(reedline::PromptEditMode::Default);
        let expected = format_indicator();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_multiline_indicator() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_multiline_indicator();
        let expected = get_multiline_indicator();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_history_search_indicator_passing() {
        let prompt = AgentChatPrompt::default();
        let history_search = reedline::PromptHistorySearch {
            status: PromptHistorySearchStatus::Passing,
            term: "test-term".to_string(),
        };
        let actual = prompt.render_prompt_history_search_indicator(history_search);
        let expected = " (reverse-search: test-term) ";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_history_search_indicator_failing() {
        let prompt = AgentChatPrompt::default();
        let history_search = reedline::PromptHistorySearch {
            status: PromptHistorySearchStatus::Failing,
            term: "test-term".to_string(),
        };
        let actual = prompt.render_prompt_history_search_indicator(history_search);
        let expected = " (failing reverse-search: test-term) ";
        assert_eq!(actual, expected);
    }
}
