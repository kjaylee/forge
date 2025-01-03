use derive_setters::Setters;
use forge_tool::ToolDefinition;
use serde::{Deserialize, Serialize};
use serde_json::json;
use utoipa::ToSchema;

use super::{CompletionMessage, Role};

/// Represents a request being made to the LLM provider. By default the request
/// is created with assuming the model supports use of external tools.
#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize, Setters, ToSchema)]
#[schema(example = json!({"messages": [], "model": "gpt-4", "tools": []}))]
pub struct Request {
    pub messages: Vec<CompletionMessage>,
    #[schema(value_type = String)]
    pub model: ModelId,
    pub tools: Vec<ToolDefinition>,
}

impl Request {
    pub fn new(id: ModelId) -> Self {
        Request { messages: vec![], tools: vec![], model: id }
    }

    pub fn add_tool(mut self, tool: impl Into<ToolDefinition>) -> Self {
        let tool = tool;
        let tool: ToolDefinition = tool.into();
        self.tools.push(tool);

        self
    }

    pub fn add_message(mut self, content: impl Into<CompletionMessage>) -> Self {
        self.messages.push(content.into());
        self
    }

    pub fn extend_tools(mut self, tools: Vec<impl Into<ToolDefinition>>) -> Self {
        self.tools.extend(tools.into_iter().map(Into::into));
        self
    }

    pub fn extend_messages(mut self, messages: Vec<impl Into<CompletionMessage>>) -> Self {
        self.messages.extend(messages.into_iter().map(Into::into));
        self
    }

    /// Updates the set system message
    pub fn set_system_message(mut self, content: impl Into<String>) -> Self {
        if self.messages.is_empty() {
            self.add_message(CompletionMessage::system(content.into()))
        } else {
            if let Some(CompletionMessage::ContentMessage(content_message)) =
                self.messages.get_mut(0)
            {
                if content_message.role == Role::System {
                    content_message.content = content.into();
                } else {
                    self.messages
                        .insert(0, CompletionMessage::system(content.into()));
                }
            }

            self
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Setters, ToSchema)]
#[schema(example = json!({"id": "gpt-4", "name": "GPT-4"}))]
pub struct Model {
    #[schema(value_type = String)]
    pub id: ModelId,
    pub name: String,
    pub description: Option<String>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, Hash, Eq, ToSchema)]
#[schema(example = "gpt-4")]
#[serde(transparent)]
pub struct ModelId(String);

impl ModelId {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for ModelId {
    fn default() -> Self {
        ModelId("openai/gpt-3.5-turbo".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_override_system_message() {
        let request = Request::new(ModelId::default())
            .add_message(CompletionMessage::system("Initial system message"))
            .set_system_message("Updated system message");

        assert_eq!(
            request.messages[0],
            CompletionMessage::system("Updated system message")
        );
    }

    #[test]
    fn test_set_system_message() {
        let request = Request::new(ModelId::default()).set_system_message("A system message");

        assert_eq!(
            request.messages[0],
            CompletionMessage::system("A system message")
        );
    }

    #[test]
    fn test_insert_system_message() {
        let request = Request::new(ModelId::default())
            .add_message(CompletionMessage::user("Do something"))
            .set_system_message("A system message");

        assert_eq!(
            request.messages[0],
            CompletionMessage::system("A system message")
        );
    }
}
