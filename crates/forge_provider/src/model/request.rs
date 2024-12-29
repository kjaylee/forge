use derive_setters::Setters;
use forge_tool::ToolDefinition;
use serde::{Deserialize, Serialize};

use super::RequestMessage;

/// Represents a request being made to the LLM provider
#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize, Setters)]
pub struct Request {
    pub messages: Vec<RequestMessage>,
    pub model: ModelId,    
    pub tools: Vec<ToolDefinition>,
}

impl Request {
    pub fn new(id: ModelId) -> Self {
        Request { messages: vec![], tools: vec![], model: id }
    }

    pub fn add_tool(mut self, tool: impl Into<ToolDefinition>) -> Self {
        self.add_tool_mut(tool);
        self
    }

    pub fn add_message(mut self, message: impl Into<RequestMessage>) -> Self {
        self.add_message_mut(message);
        self
    }

    pub fn extend_tools(mut self, tools: Vec<impl Into<ToolDefinition>>) -> Self {
        self.extend_tools_mut(tools);
        self
    }

    pub fn extend_messages(mut self, messages: Vec<impl Into<RequestMessage>>) -> Self {
        self.extend_messages_mut(messages);
        self
    }

    pub fn add_tool_mut(&mut self, tool: impl Into<ToolDefinition>) {
        let tool: ToolDefinition = tool.into();
        self.tools.push(tool);
    }

    pub fn add_message_mut(&mut self, message: impl Into<RequestMessage>) {
        self.messages.push(message.into());
    }

    pub fn extend_tools_mut(&mut self, tools: Vec<impl Into<ToolDefinition>>) {
        self.tools.extend(tools.into_iter().map(Into::into));
    }

    pub fn extend_messages_mut(&mut self, messages: Vec<impl Into<RequestMessage>>) {
        self.messages.extend(messages.into_iter().map(Into::into));
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Setters)]
pub struct Model {
    pub id: ModelId,
    pub name: String,
    pub description: Option<String>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ModelId(String);

impl Default for ModelId {
    fn default() -> Self {
        ModelId("openai/gpt-3.5-turbo".to_string())
    }
}
