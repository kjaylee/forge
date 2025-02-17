use forge_domain::ModelId;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct ListModelResponse {
    pub data: Vec<Model>,
    has_more: bool,
    first_id: String,
    last_id: String,
}

#[derive(Deserialize)]
pub struct Model {
    r#type: String,
    id: String,
    display_name: String,
    created_at: String,
}

impl From<Model> for forge_domain::Model {
    fn from(value: Model) -> Self {
        Self {
            id: ModelId::new(value.id),
            name: value.display_name,
            description: None,
            context_length: None,
        }
    }
}

#[derive(Deserialize)]
pub struct Response {
    content: Vec<Content>,
    id: String,
    model: String,
    role: Role,
    stop_reason: Option<StopReason>,
    stop_sequence: Option<String>,
    r#type: ResponseType,
    usage: Usage,
}

#[derive(Deserialize)]
struct Usage {
    cache_creation_input_tokens: Option<u64>,
    cache_read_input_tokens: Option<u64>,
    input_tokens: Option<u64>,
    output_tokens: Option<u64>,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum ResponseType {
    Message,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum StopReason {
    EndTurn,
    MaxTokens,
    StopSequence,
    ToolUse,
}

#[derive(Deserialize)]
enum Role {
    #[serde(rename = "assistant")]
    Assistant,
}

#[derive(Deserialize)]
enum Content {
    Text {
        text: String,
        r#type: TextContentType,
    },
    ToolUse {
        id: String,
        input: serde_json::Value,
        name: String,
        r#type: ToolUseContentType,
    },
}

#[derive(Deserialize)]
enum TextContentType {
    #[serde(rename = "text")]
    Text,
}

#[derive(Deserialize)]
enum ToolUseContentType {
    #[serde(rename = "tool_use")]
    ToolUse,
}

#[cfg(test)]
mod tests {
    use super::ListModelResponse;

    #[test]
    fn test_model_deser() {
        let input = r#"{
            "data": [
                {
                    "type": "model",
                    "id": "claude-3-5-sonnet-20241022",
                    "display_name": "Claude 3.5 Sonnet (New)",
                    "created_at": "2024-10-22T00:00:00Z"
                },
                {
                    "type": "model",
                    "id": "claude-3-5-haiku-20241022",
                    "display_name": "Claude 3.5 Haiku",
                    "created_at": "2024-10-22T00:00:00Z"
                }
            ],
            "has_more": false,
            "first_id": "claude-3-5-sonnet-20241022",
            "last_id": "claude-3-opus-20240229"
        }"#;
        let response = serde_json::from_str::<ListModelResponse>(input);
        assert!(response.is_ok());
        assert!(response.unwrap().data.len() == 2);
    }
}
