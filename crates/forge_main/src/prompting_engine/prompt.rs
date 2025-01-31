use std::borrow::Cow;

use derive_setters::Setters;
use forge_domain::Usage;
use nu_ansi_term::{Color, Style};
use reedline::{Prompt, PromptHistorySearchStatus};

// Constants
pub const MAX_LEN: usize = 30;
const AI_INDICATOR: &str = "⚡";
const MULTILINE_INDICATOR: &str = "::: ";
const RIGHT_CHEVRON: &str = "❯";

// // outputs: `➜ FORGE ⚡ `
// fn base_prompt() -> Cow<'static, str> {
//     format!(
//         "{} {}",
//         Style::new()::fg(Color::LightGreen).paint(ARROW),
//         Style::new()::fg(Color::Cyan).paint(SHELL_NAME)
//     )
// }

// // outputs: `(title)`
// fn format_title(title: &str) -> Cow<str> {
//     let title = title.chars().take(MAX_LEN).collect::<String>();
//     format!(
//         "{}{}{}",
//         Style::new()::fg(Color::Blue).paint(LEFT_PAREN),
//         Style::new()::fg(Color::Red).paint(title),
//         Style::new()::fg(Color::Blue).paint(RIGHT_PAREN)
//     )
// }

// // outputs: `[end]`
// fn format_end(end: &str) -> Cow<str> {
//     format!(
//         " {}{}{}",
//         Style::new()::fg(Color::DarkGray).paint(LEFT_BRACKET),
//         Style::new()::fg(Color::DarkGray).paint(end),
//         Style::new()::fg(Color::DarkGray).paint(RIGHT_BRACKET)
//     )
// }

// // outputs: ` ⚡ `
// fn format_indicator() -> Cow<str> {
//     format!(" {} ", Style::new()::fg(Color::LightYellow).paint(AI_INDICATOR))
// }

// outputs: `::: `
// fn get_multiline_indicator() -> &'static str {
//     MULTILINE_INDICATOR
// }

/// Very Specialized Prompt for the Agent Chat
#[derive(Clone, Default, Setters)]
#[setters(strip_option, borrow_self)]
pub struct ForgePrompt {
    title: Option<String>,
    usage: Option<Usage>,
}

impl Prompt for ForgePrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        if let Some(title) = self.title.as_ref() {
            let title = title.chars().take(MAX_LEN).collect::<String>();
            Cow::Owned(format!(
                "{AI_INDICATOR} {}",
                Style::new().fg(Color::Cyan).paint(title),
            ))
        } else {
            Cow::Borrowed(AI_INDICATOR)
        }
    }

    fn render_prompt_right(&self) -> Cow<str> {
        if let Some(usage) = self.usage.as_ref() {
            let usage_text = format!(
                "[{}/{}/{}]",
                usage.prompt_tokens, usage.completion_tokens, usage.total_tokens
            );
            Cow::Owned(
                Style::new()
                    .bold()
                    .fg(Color::DarkGray)
                    .paint(usage_text)
                    .to_string(),
            )
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_indicator(&self, _prompt_mode: reedline::PromptEditMode) -> Cow<str> {
        if self.title.is_some() {
            Cow::Owned(
                Style::new()
                    .fg(Color::LightYellow)
                    .paint(format!(" {RIGHT_CHEVRON} "))
                    .to_string(),
            )
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed(MULTILINE_INDICATOR)
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

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_render_prompt_left_with_title() {
//         let prompt =
// AgentChatPrompt::default().start(Some("test-title".to_string()));         let
// actual = prompt.render_prompt_left();         let expected = format!("{} {}",
// base_prompt_indicator(), format_title("test-title"));         assert_eq!
// (actual, expected);     }

//     #[test]
//     fn test_render_prompt_left_without_title() {
//         let prompt = AgentChatPrompt::default();
//         let actual = prompt.render_prompt_left();
//         let expected = base_prompt_indicator();
//         assert_eq!(actual, expected);
//     }

//     #[test]
//     fn test_render_prompt_left_with_long_title() {
//         let long_title = "a".repeat(MAX_LEN + 10);
//         let prompt =
// AgentChatPrompt::default().start(Some(long_title.clone()));         let
// actual = prompt.render_prompt_left();         let truncated = format!("{}{}",
// "a".repeat(MAX_LEN), "...");         let expected = format!("{} {}",
// base_prompt_indicator(), format_title(&truncated));         assert_eq!
// (actual, expected);     }

//     #[test]
//     fn test_render_prompt_right_with_end() {
//         let prompt =
// AgentChatPrompt::default().end(Some("test-end".to_string()));         let
// actual = prompt.render_prompt_right();         let expected =
// format_end("test-end");         assert_eq!(actual, expected);
//     }

//     #[test]
//     fn test_render_prompt_right_without_end() {
//         let prompt = AgentChatPrompt::default();
//         let actual = prompt.render_prompt_right();
//         let expected = "";
//         assert_eq!(actual, expected);
//     }

//     #[test]
//     fn test_render_prompt_indicator() {
//         let prompt = AgentChatPrompt::default();
//         let actual =
// prompt.render_prompt_indicator(reedline::PromptEditMode::Default);
//         let expected = format_indicator();
//         assert_eq!(actual, expected);
//     }

//     #[test]
//     fn test_render_prompt_multiline_indicator() {
//         let prompt = AgentChatPrompt::default();
//         let actual = prompt.render_prompt_multiline_indicator();
//         let expected = get_multiline_indicator();
//         assert_eq!(actual, expected);
//     }

//     #[test]
//     fn test_render_prompt_history_search_indicator_passing() {
//         let prompt = AgentChatPrompt::default();
//         let history_search = reedline::PromptHistorySearch {
//             status: PromptHistorySearchStatus::Passing,
//             term: "test-term".to_string(),
//         };
//         let actual =
// prompt.render_prompt_history_search_indicator(history_search);         let
// expected = " (reverse-search: test-term) ";         assert_eq!(actual,
// expected);     }

//     #[test]
//     fn test_render_prompt_history_search_indicator_failing() {
//         let prompt = AgentChatPrompt::default();
//         let history_search = reedline::PromptHistorySearch {
//             status: PromptHistorySearchStatus::Failing,
//             term: "test-term".to_string(),
//         };
//         let actual =
// prompt.render_prompt_history_search_indicator(history_search);         let
// expected = " (failing reverse-search: test-term) ";         assert_eq!
// (actual, expected);     }
// }
