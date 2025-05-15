use crate::antinomy::request::Request;
use crate::antinomy::tool_choice::ToolChoice;
use crate::antinomy::transformers::Transformer;

pub struct SetToolChoice {
    choice: ToolChoice,
}

impl SetToolChoice {
    pub fn new(choice: ToolChoice) -> Self {
        Self { choice }
    }
}

impl Transformer for SetToolChoice {
    fn transform(&self, mut request: Request) -> Request {
        request.tool_choice = Some(self.choice.clone());
        request
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::{Context, ModelId};

    use super::*;

    #[test]
    fn test_gemini_transformer_tool_strategy() {
        let context = Context::default();
        let request = Request::from(context).model(ModelId::new("google/gemini-pro"));

        let transformer = SetToolChoice::new(ToolChoice::Auto);
        let transformed = transformer.transform(request);

        assert_eq!(transformed.tool_choice, Some(ToolChoice::Auto));
    }
}
