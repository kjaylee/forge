use ratatui::layout::{Constraint, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Paragraph, Widget, Wrap};

use crate::widgets::spinner::Spinner;

/// Enum to differentiate between user and assistant messages
#[derive(Debug, Clone, PartialEq)]
pub enum Message {
    User(String),
    Assistant(String),
}

#[cfg(test)]
impl Message {
    /// Get the content of the message regardless of type
    pub fn content(&self) -> &str {
        match self {
            Message::User(content) => content,
            Message::Assistant(content) => content,
        }
    }

    /// Check if this is a user message
    pub fn is_user(&self) -> bool {
        matches!(self, Message::User(_))
    }

    /// Check if this is an assistant message
    pub fn is_assistant(&self) -> bool {
        matches!(self, Message::Assistant(_))
    }
}

#[derive(Default)]
pub struct MessageList {
    pub messages: Vec<Message>,
    pub spinner: Spinner,
}

impl MessageList {
    pub fn new(messages: Vec<Message>) -> Self {
        Self { messages, spinner: Spinner::default() }
    }

    /// Create MessageList from Vec<String> for backward compatibility
    #[cfg(test)]
    pub fn from_strings(messages: Vec<String>) -> Self {
        let messages = messages
            .into_iter()
            .map(Message::User) // Default to user messages for backward compatibility
            .collect();
        Self { messages, spinner: Spinner::default() }
    }

    /// Convert messages to styled lines for rendering
    fn messages_to_lines(&self) -> Vec<Line<'_>> {
        self.messages
            .iter()
            .map(|message| match message {
                Message::User(content) => {
                    Line::from(vec![Span::styled(content, Style::default().dim().bold())])
                }
                Message::Assistant(content) => Line::from(Span::raw(content)),
            })
            .collect()
    }
}

impl Widget for MessageList {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        if self.messages.is_empty() {
            Paragraph::new(include_str!("./banner.txt"))
                .fg(Color::DarkGray)
                .centered()
                .wrap(Wrap { trim: false })
                .render(area, buf);
        } else {
            let [message_cont, loader_cont] =
                Layout::vertical([Constraint::Fill(0), Constraint::Max(1)]).areas(area);

            Paragraph::new(self.messages_to_lines())
                .wrap(Wrap { trim: false })
                .render(message_cont, buf);

            self.spinner.render(loader_cont, buf);
        };
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_message_content() {
        let user_message = Message::User("Hello".to_string());
        let assistant_message = Message::Assistant("Hi there".to_string());

        assert_eq!(user_message.content(), "Hello");
        assert_eq!(assistant_message.content(), "Hi there");
    }

    #[test]
    fn test_message_type_checks() {
        let user_message = Message::User("Hello".to_string());
        let assistant_message = Message::Assistant("Hi there".to_string());

        assert!(user_message.is_user());
        assert!(!user_message.is_assistant());
        assert!(assistant_message.is_assistant());
        assert!(!assistant_message.is_user());
    }

    #[test]
    fn test_message_list_new() {
        let messages = vec![
            Message::User("Hello".to_string()),
            Message::Assistant("Hi there".to_string()),
        ];
        let message_list = MessageList::new(messages.clone());

        assert_eq!(message_list.messages, messages);
    }

    #[test]
    fn test_message_list_from_strings() {
        let strings = vec!["Hello".to_string(), "World".to_string()];
        let message_list = MessageList::from_strings(strings);

        let expected = vec![
            Message::User("Hello".to_string()),
            Message::User("World".to_string()),
        ];
        assert_eq!(message_list.messages, expected);
    }

    #[test]
    fn test_messages_to_lines() {
        let messages = vec![
            Message::User("Hello".to_string()),
            Message::Assistant("Hi there".to_string()),
        ];
        let message_list = MessageList::new(messages);
        let lines = message_list.messages_to_lines();

        assert_eq!(lines.len(), 2);
        // We can't easily test the exact Line content due to styling,
        // but we can verify the count is correct
    }

    #[test]
    fn test_empty_message_list() {
        let message_list = MessageList::default();
        assert!(message_list.messages.is_empty());
    }
}
