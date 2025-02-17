use derive_setters::Setters;
use forge_domain::ContextMessage;
use serde::Serialize;

#[derive(Serialize, Default, Setters)]
#[setters(into, strip_option)]
pub struct Request {
    max_tokens: u64,
    messages: Vec<Message>,
    model: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    metadata: Option<Metadata>,
    #[serde(skip_serializing_if = "Option::is_none")]
    stop_sequence: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    stream: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    system: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    temperature: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    tool_choice: Option<ToolChoice>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tools: Vec<ToolDefinition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    top_k: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    top_p: Option<f32>,
}

impl From<forge_domain::Context> for Request {
    fn from(mut request: forge_domain::Context) -> Self {
        // only 1st system message is supported.
        let system = request.messages.iter().find_map(|message| {
            if let ContextMessage::ContentMessage(chat_message) = message {
                if chat_message.role == forge_domain::Role::System {
                    Some(chat_message.content.clone())
                } else {
                    None
                }
            } else {
                None
            }
        });
        // anthropic has only 2 roles. i.e user and assistant. so we need to filter out
        // system messages.
        request.messages.retain(|message| {
                if let ContextMessage::ContentMessage(chat_message) = message {
                    chat_message.role != forge_domain::Role::System
                } else {
                    true
                }
            });

        Self {
            messages: request.messages.iter().map(Message::from).collect(),
            tools: request
                .tools
                .into_iter()
                .map(ToolDefinition::from)
                .collect::<Vec<_>>(),
            system,
            tool_choice: request.tool_choice.map(ToolChoice::from),
            ..Default::default()
        }
    }
}

#[derive(Serialize)]
pub struct Metadata {
    #[serde(skip_serializing_if = "Option::is_none")]
    user_id: Option<String>,
}

#[derive(Serialize)]
pub struct Message {
    content: Vec<Content>,
    role: Role,
}

impl From<&ContextMessage> for Message {
    fn from(value: &ContextMessage) -> Self {
        match &value {
            ContextMessage::ContentMessage(chat_message) => {
                let mut contents = vec![];
                contents.push(Content::String(chat_message.content.clone()));
                // TODO: what if the chat_message has tool_calls???
                match chat_message.role {
                    forge_domain::Role::User => Message { role: Role::User, content: contents },
                    forge_domain::Role::Assistant => {
                        Message { role: Role::Assistant, content: contents }
                    }
                    forge_domain::Role::System => {
                        // note: system role messages are already filtered out.
                        // so this state is unreachable.
                        unreachable!()
                    }
                }
            }
            ContextMessage::ToolMessage(tool_result) => Message {
                role: Role::Assistant, // TODO: verify the role type once for toolcall.
                // TODO: drop unwrap
                content: vec![Content::Object(tool_result.try_into().unwrap())],
            },
        }
    }
}

#[derive(Serialize)]
#[serde(untagged)]
enum Content {
    String(String),
    Object(Object),
}

#[derive(Serialize)]
#[serde(untagged)]
enum Object {
    Text {
        text: String,
        // only `text` type avail.
        r#type: ObjectType,
        #[serde(skip_serializing_if = "Option::is_none")]
        cache_control: Option<CacheControl>,
    },
    Image {
        // add support for image type later.
    },
    ToolUse {
        id: String,
        input: serde_json::Value,
        name: String,
        r#type: ToolUseType,
        #[serde(skip_serializing_if = "Option::is_none")]
        cache_control: Option<CacheControl>,
    },
    ToolResult {
        tool_use_id: String,
        r#type: ToolResultType,
        #[serde(skip_serializing_if = "Option::is_none")]
        cache_control: Option<CacheControl>,
        #[serde(skip_serializing_if = "Option::is_none")]
        content: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        is_error: Option<bool>,
    },
    Document {
        // TODO: add support for doc type.
    },
}

impl TryFrom<&forge_domain::ToolResult> for Object {
    type Error = anyhow::Error;
    fn try_from(value: &forge_domain::ToolResult) -> std::result::Result<Self, Self::Error> {
        let call_id = value
            .call_id
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("`call_id` is required for tool_result"))?;
        Ok(Object::ToolResult {
            tool_use_id: call_id.as_str().to_string(),
            r#type: ToolResultType::ToolResult,
            cache_control: None,
            content: Some(value.content.clone()),
            is_error: Some(value.is_error),
        })
    }
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum ObjectType {
    Text,
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum CacheControl {
    Ephemeral,
}

#[derive(Serialize)]
#[serde(untagged)]
pub enum ToolUseType {
    #[serde(rename = "tool_use")]
    ToolUse,
}

#[derive(Serialize)]
#[serde(untagged)]
pub enum ToolResultType {
    #[serde(rename = "tool_result")]
    ToolResult,
}

#[derive(Serialize)]
#[serde(untagged)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    User,
    Assistant,
}

#[derive(Serialize)]
#[serde(untagged)]
pub enum ToolChoice {
    Auto {
        r#type: ToolChoiceAuto,
        #[serde(skip_serializing_if = "Option::is_none")]
        disable_parallel_tool_use: Option<bool>,
    },
    Any {
        r#type: ToolChoiceAny,
        #[serde(skip_serializing_if = "Option::is_none")]
        disable_parallel_tool_use: Option<bool>,
    },
    Tool {
        name: String,
        r#type: ToolChoiceTool,
        #[serde(skip_serializing_if = "Option::is_none")]
        disable_parallel_tool_use: Option<bool>,
    },
}

impl From<forge_domain::ToolChoice> for ToolChoice {
    fn from(value: forge_domain::ToolChoice) -> Self {
        match value {
            forge_domain::ToolChoice::Auto => ToolChoice::Auto {
                r#type: ToolChoiceAuto::Auto,
                disable_parallel_tool_use: None,
            },
            forge_domain::ToolChoice::Call(tool_name) => ToolChoice::Tool {
                name: tool_name.into_string(),
                r#type: ToolChoiceTool::Tool,
                disable_parallel_tool_use: None,
            },
            forge_domain::ToolChoice::Required => {
                // since we don't have this type, we use auto type to let the llm decide.
                ToolChoice::Auto {
                    r#type: ToolChoiceAuto::Auto,
                    disable_parallel_tool_use: None,
                }
            }
            forge_domain::ToolChoice::None => {
                ToolChoice::Any { r#type: ToolChoiceAny::Any, disable_parallel_tool_use: None }
            }
        }
    }
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum ToolChoiceAuto {
    Auto,
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum ToolChoiceAny {
    Any,
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum ToolChoiceTool {
    Tool,
}

#[derive(Serialize)]
pub struct ToolDefinition {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    description: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    cache_control: Option<CacheControl>,
    input_schema: serde_json::Value,
    r#type: ToolDefinitionType,
}

impl From<forge_domain::ToolDefinition> for ToolDefinition {
    fn from(value: forge_domain::ToolDefinition) -> Self {
        ToolDefinition {
            name: value.name.into_string(),
            description: Some(value.description),
            cache_control: None,
            input_schema: serde_json::to_value(value.input_schema).unwrap(),
            r#type: ToolDefinitionType::Custom,
        }
    }
}

#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum ToolDefinitionType {
    Custom,
}
