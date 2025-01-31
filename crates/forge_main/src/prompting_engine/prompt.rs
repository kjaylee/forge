use std::borrow::Cow;

use derive_setters::Setters;
use nu_ansi_term::{Color, Style};
use reedline::{Prompt, PromptHistorySearchStatus};

// cap the title by `MAX_LEN` chars and show ellipsis at the end.
const MAX_LEN: usize = 30;

/// Very Specialized Prompt for the Agent Chat
#[derive(Clone, Default, Setters)]
pub struct AgentChatPrompt {
    start: Option<String>,
    end: Option<String>,
}

impl Prompt for AgentChatPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        if let Some(title) = self.start.as_ref() {
            // TODO: cap the title by 15 chars else show ellipsis at the end.
            let truncated = if title.chars().count() > MAX_LEN {
                format!("{}...", title.chars().take(MAX_LEN).collect::<String>())
            } else {
                title.to_string()
            };

            Cow::Owned(format!(
                "{} {} {}{}{}",
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::LightGreen)
                    .paint("➜"),
                Style::new().fg(Color::Cyan).bold().paint("FORGE"),
                Style::new().fg(Color::Blue).bold().paint("("),
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::Red)
                    .paint(truncated),
                Style::new().fg(Color::Blue).bold().paint(")")
            ))
        } else {
            Cow::Owned(format!(
                "{} {}",
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::LightGreen)
                    .paint("➜"),
                Style::new().fg(Color::Cyan).bold().paint("FORGE"),
            ))
        }
    }

    fn render_prompt_right(&self) -> Cow<str> {
        if let Some(end) = self.end.as_ref() {
            Cow::Owned(format!(
                " {}{}{}",
                Style::new().fg(Color::DarkGray).bold().paint("["),
                Style::new()
                    .reset_before_style()
                    .fg(Color::DarkGray)
                    .bold()
                    .paint(end),
                Style::new().fg(Color::DarkGray).bold().paint("]"),
            ))
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_indicator(&self, _prompt_mode: reedline::PromptEditMode) -> Cow<str> {
        Cow::Owned(format!(
            " {} ",
            Style::new().fg(Color::LightYellow).bold().paint("⚡")
        ))
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed("::: ")
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
            "{} {} {}{}{}",
            Style::new()
                .reset_before_style()
                .bold()
                .fg(Color::LightGreen)
                .paint("➜"),
            Style::new().fg(Color::Cyan).bold().paint("FORGE"),
            Style::new().fg(Color::Blue).bold().paint("("),
            Style::new()
                .reset_before_style()
                .bold()
                .fg(Color::Red)
                .paint("test-title"),
            Style::new().fg(Color::Blue).bold().paint(")")
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_without_title() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_left();
        let expected = format!(
            "{} {}",
            Style::new()
                .reset_before_style()
                .bold()
                .fg(Color::LightGreen)
                .paint("➜"),
            Style::new().fg(Color::Cyan).bold().paint("FORGE")
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_left_with_long_title() {
        let long_title = "a".repeat(MAX_LEN + 10);
        let prompt = AgentChatPrompt::default().start(Some(long_title.clone()));
        let actual = prompt.render_prompt_left();
        let truncated = format!("{}{}", "a".repeat(MAX_LEN), "...");
        let expected = format!(
            "{} {} {}{}{}",
            Style::new()
                .reset_before_style()
                .bold()
                .fg(Color::LightGreen)
                .paint("➜"),
            Style::new().fg(Color::Cyan).bold().paint("FORGE"),
            Style::new().fg(Color::Blue).bold().paint("("),
            Style::new()
                .reset_before_style()
                .bold()
                .fg(Color::Red)
                .paint(truncated),
            Style::new().fg(Color::Blue).bold().paint(")")
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_right_with_end() {
        let prompt = AgentChatPrompt::default().end(Some("test-end".to_string()));
        let actual = prompt.render_prompt_right();
        let expected = format!(
            " {}{}{}",
            Style::new().fg(Color::DarkGray).bold().paint("["),
            Style::new()
                .reset_before_style()
                .fg(Color::DarkGray)
                .bold()
                .paint("test-end"),
            Style::new().fg(Color::DarkGray).bold().paint("]")
        );
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
        let expected = format!(
            " {} ",
            Style::new().fg(Color::LightYellow).bold().paint("⚡")
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_prompt_multiline_indicator() {
        let prompt = AgentChatPrompt::default();
        let actual = prompt.render_prompt_multiline_indicator();
        let expected = "::: ";
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
