use std::borrow::Cow;

use derive_setters::Setters;
use reedline::{Prompt, PromptHistorySearchStatus};

use super::style;

/// Very Specialized Prompt for the Agent Chat
#[derive(Clone, Default, Setters)]
pub struct AgentChatPrompt {
    start: Option<String>,
    end: Option<String>,
}

impl Prompt for AgentChatPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        if let Some(title) = self.start.as_ref() {
            let truncated = if title.chars().count() > style::MAX_LEN {
                format!(
                    "{}{}",
                    title.chars().take(style::MAX_LEN).collect::<String>(),
                    "..."
                )
            } else {
                title.to_string()
            };

            Cow::Owned(format!(
                "{} {}",
                style::base_prompt_indicator(),
                style::format_title(&truncated)
            ))
        } else {
            Cow::Owned(style::base_prompt_indicator())
        }
    }

    fn render_prompt_right(&self) -> Cow<str> {
        if let Some(end) = self.end.as_ref() {
            Cow::Owned(style::format_end(end))
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_indicator(&self, _prompt_mode: reedline::PromptEditMode) -> Cow<str> {
        Cow::Owned(style::format_indicator())
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed(style::get_multiline_indicator())
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
        let expected = format!(
            "{} {}",
            style::base_prompt_indicator(),
            style::format_title("test-title")
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_without_title() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_left();
        let expected = style::base_prompt_indicator();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_with_long_title() {
        let long_title = "a".repeat(style::MAX_LEN + 10);
        let prompt = AgentChatPrompt::default().start(Some(long_title.clone()));
        let actual = prompt.render_prompt_left();
        let truncated = format!("{}{}", "a".repeat(style::MAX_LEN), "...");
        let expected = format!(
            "{} {}",
            style::base_prompt_indicator(),
            style::format_title(&truncated)
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_right_with_end() {
        let prompt = AgentChatPrompt::default().end(Some("test-end".to_string()));
        let actual = prompt.render_prompt_right();
        let expected = style::format_end("test-end");
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
        let expected = style::format_indicator();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_multiline_indicator() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_multiline_indicator();
        let expected = style::get_multiline_indicator();
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
