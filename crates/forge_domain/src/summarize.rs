//! Context Summarization:
//! - Break the conversation into "turns"
//! - A turn is a sequence of messages where the first message is a user message
//! - Summarization happens for each turn independently with the oldest turn
//!   getting the highest priority.
//! - Summarization is done by removing all assistant/tool messages within a
//!   turn and replacing it with a summary as an assistant message.
//! - If a turn summary isn't enough to hit the thresholds, then the next turn
//!   is summarized.
//! - If after summarization of all the turns the threshold is still not met,
//!   then all the turns have to summarized again (summary of summary)
//! - NOTE: User and System messages are never summarized

use std::ops::Range;

use crate::{Context, ContextMessage, Role};

pub struct Summarize<'context> {
    context: &'context mut Context,
    token_limit: usize,
    // TODO: use a persistent cache to avoid re-summarizing
}

impl<'context> Summarize<'context> {
    pub fn new(context: &'context mut Context, token_limit: usize) -> Self {
        Self { context, token_limit }
    }

    fn replace(&mut self, content: impl ToString, range: Range<usize>) {
        // TODO: improve the quality of summary message
        let content = format!("\n<work_summary>\n{}\n</work_summary>", content.to_string());
        let message = ContextMessage::assistant(content, None);

        self.context
            .messages
            .splice(range.clone(), std::iter::empty());
        self.context.messages.insert(range.start, message);
    }

    /// Get a replaceable item while the total token count is above the limit
    pub fn summarize(&mut self) -> Option<Summary<'_, 'context>> {
        let total = token_count(&self.context.to_text());

        if total <= self.token_limit {
            return None;
        }

        // get the next range that can be summarized.
        next_turn(&self.context).and_then(|turn| {
            if turn.end >= self.context.messages.len() {
                // if it's the on-going user message, then don't summarize it.
                None
            } else {
                Some(Summary { summarize: self, next_turn: turn })
            }
        })
    }
}

pub struct Summary<'this, 'context> {
    summarize: &'this mut Summarize<'context>,
    next_turn: Range<usize>,
}

impl Summary<'_, '_> {
    pub fn set(&mut self, message: impl ToString) {
        self.summarize.replace(message, self.next_turn.clone());
    }

    pub fn get(&self) -> String {
        Context::default()
            .messages(self.summarize.context.messages[self.next_turn.clone()].to_vec())
            .to_text()
    }
}

// TODO: this is a quick hack to get a ballpark token count
fn token_count(text: &str) -> usize {
    text.split_whitespace().count() * 75 / 100
}

/// Finds the first turn of a user message in the given context.
///
/// Returns a range of indices representing the first user message
/// up to (but not including) the next user message. If there's no
/// second user message, the range extends to the end of messages.
fn next_turn(context: &Context) -> Option<Range<usize>> {
    let start = context
        .messages
        .iter()
        .position(|m| m.has_role(Role::User))?;
    let end = context
        .messages
        .iter()
        .skip(start + 1)
        .position(|m| m.has_role(Role::User));

    Some(start..end.map_or(context.messages.len(), |e| start + 1 + e))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper function to create a test context with specified messages
    fn create_test_context(messages: Vec<ContextMessage>) -> Context {
        Context::default().messages(messages)
    }

    #[test]
    fn test_turns_empty_context() {
        let context = create_test_context(vec![]);
        let turns_result = next_turn(&context);
        assert!(turns_result.is_none());
    }

    #[test]
    fn test_summarize_no_summary_needed() {
        let mut context = create_test_context(vec![
            ContextMessage::user("Short message".to_string()),
            ContextMessage::assistant("Brief response".to_string(), None),
        ]);
        let mut summarize = Summarize::new(&mut context, 1000);
        assert!(summarize.summarize().is_none());
    }

    #[test]
    fn test_next_turn_when_theres_no_user_message() {
        let context = create_test_context(vec![
            ContextMessage::system("System message".to_string()),
            ContextMessage::assistant("Assistant message".to_string(), None),
            ContextMessage::assistant("Another assistant message".to_string(), None),
            ContextMessage::assistant("Another assistant message".to_string(), None),
        ]);
        let turns_result = next_turn(&context);
        assert!(turns_result.is_none());
    }

    #[test]
    fn test_next_turn_when_user_message_is_at_last_index() {
        let context = create_test_context(vec![
            ContextMessage::system("System message".to_string()),
            ContextMessage::assistant("Assistant message".to_string(), None),
            ContextMessage::assistant("Another assistant message".to_string(), None),
            ContextMessage::assistant("Another assistant message".to_string(), None),
            ContextMessage::user("User message".to_string()),
        ]);
        let turns_result = next_turn(&context).unwrap();
        assert_eq!(turns_result, 4..5);
    }

    #[test]
    fn test_summarize_with_summary_needed() {
        let mut context = create_test_context(vec![
            ContextMessage::system("I'm expert at solving problems".to_string()),
            ContextMessage::user("can you tell me what's the time in india right now?".to_string()),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::user("okay, what are tools avail to you?".to_string()),
            ContextMessage::assistant("i have only one tool avail to me and it's `shell` tool.".to_string(), None),
            ContextMessage::user("can you use this tool to figure out if this project compiles or not?".to_string()),
        ]);
        let mut summarize = Summarize::new(&mut context, 100);
        let mut summary = summarize.summarize().expect("Should require summarization");
        summary.set("User is asking about the time and tools available");

        assert_eq!(context.messages.len(), 5);
        assert_eq!(context.messages, vec![
            ContextMessage::system("I'm expert at solving problems".to_string()),
            ContextMessage::assistant("\n<work_summary>\nUser is asking about the time and tools available\n</work_summary>".to_string(), None),
            ContextMessage::user("okay, what are tools avail to you?".to_string()),
            ContextMessage::assistant("i have only one tool avail to me and it's `shell` tool.".to_string(), None),
            ContextMessage::user("can you use this tool to figure out if this project compiles or not?".to_string()),
        ]);
    }

    #[test]
    fn test_summarize_with_one_user_and_all_assistant() {
        let mut context = create_test_context(vec![
            ContextMessage::system("I'm expert at solving problems".to_string()),
            ContextMessage::user("can you tell me what's the time in india right now?".to_string()),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
            ContextMessage::assistant("yes, i will use shell tool to get the time, please use `date` command to get the time.".to_string(), None),
        ]);
        let mut summarize = Summarize::new(&mut context, 100);
        let mut summary = summarize.summarize().expect("Should require summarization");
        summary.set("User is asking about the time and tools available");

        assert_eq!(context.messages.len(), 2);
        assert_eq!(context.messages, vec![
            ContextMessage::system("I'm expert at solving problems".to_string()),
            ContextMessage::assistant("\n<work_summary>\nUser is asking about the time and tools available\n</work_summary>".to_string(), None),
        ]);
    }

    #[test]
    fn test_single_user_message_summarize() {
        let mut context = create_test_context(vec![
            ContextMessage::system("I'm expert at solving problems".to_string()),
            ContextMessage::user("can you tell me what's the time in india right now?".to_string()),
        ]);

        let mut summarize = Summarize::new(&mut context, 10);

        let summary = summarize.summarize().expect("Should require summarization");
        assert_eq!(summary.get(), "<chat_history><message role=\"User\"><content>can you tell me what's the time in india right now?</content></message></chat_history>");
    }

    #[test]
    fn test_no_message_summarize() {
        let mut context = create_test_context(vec![ContextMessage::system(
            "I'm expert at solving problems".to_string(),
        )]);
        let mut summarize = Summarize::new(&mut context, 10);
        assert!(summarize.summarize().is_none());
    }
}
