use forge_domain::{Context, Transformer};

pub struct ReasoningTransform;

impl Transformer for ReasoningTransform {
    type Value = Context;
    fn transform(&mut self, mut context: Self::Value) -> Self::Value {
        if let Some(reasoning) = context.reasoning.as_ref() {
            if reasoning.enabled.unwrap_or(false) && reasoning.max_tokens.is_some() {
                // if reasoning is enabled then we've to drop top_k and top_p
                context.top_k = None;
                context.top_p = None;
            }
        }

        context
    }
}
