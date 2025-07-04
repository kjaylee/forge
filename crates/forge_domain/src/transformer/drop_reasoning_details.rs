use crate::{Context, Transformer};

#[derive(Default)]
pub struct DropReasoningDetails;

impl Transformer for DropReasoningDetails {
    type Value = Context;
    fn transform(&mut self, mut context: Self::Value) -> Self::Value {
        context.messages.iter_mut().for_each(|message| {
            if let crate::ContextMessage::Text(text) = message {
                text.reasoning_details = None;
            }
        });

        context
    }
}
