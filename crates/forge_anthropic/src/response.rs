use forge_domain::ModelId;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct ListModelResponse {
    pub data: Vec<Model>,
}

#[derive(Deserialize)]
pub struct Model {
    id: String,
    display_name: String,
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
