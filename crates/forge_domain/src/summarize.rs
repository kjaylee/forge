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

use crate::Context;

pub struct Summarize {
    input: Context,
    output: Context,
    token_limit: usize,
}

impl Summarize {
    pub fn new(context: Context, token_limit: usize) -> Self {
        Self { input: context, output: Context::default(), token_limit }
    }

    fn replace(&mut self, message: impl ToString) {
        todo!()
    }
}

impl<'a> Iterator for &'a Summarize {
    type Item = Replace<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

pub struct Replace<'a> {
    context: Context,
    summary: &'a mut Summarize,
}

impl Replace<'_> {
    pub fn set(&mut self, message: impl ToString) {
        self.summary.replace(message);
    }

    pub fn get(&self) -> String {
        self.context.to_text()
    }
}
