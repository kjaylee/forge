use std::sync::Arc;

use forge_domain::{NamedTool, ToolCallService, ToolDescription};
use forge_tool_macros::ToolDescription;
use reqwest::{header::HeaderMap, Request};
use schemars::JsonSchema;
use serde::Deserialize;

use crate::http_client::HttpIO;

/// Request to research about a topic. The tool will use the internet to find
/// the most relevant information about the topic and return the information in
/// a readable format.
#[derive(Clone, ToolDescription)]
pub struct ResearchTool {
    api_key: String,
    model: String,
    client: Arc<dyn HttpIO>,
}

impl ResearchTool {
    pub fn new(api_key: impl ToString, model: impl ToString, client: Arc<dyn HttpIO>) -> Self {
        Self {
            api_key: api_key.to_string(),
            model: model.to_string(),
            client,
        }
    }
}

impl NamedTool for ResearchTool {
    fn tool_name(&self) -> forge_domain::ToolName {
        forge_domain::ToolName::new("research")
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    System,
    User,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Message {
    role: Role,
    content: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct PerplexityRequest {
    model: String,
    messages: Vec<Message>,
    max_tokens: Option<i32>,
    temperature: f64,
    top_p: f64,
    search_domain_filter: Vec<String>,
    return_images: bool,
    return_related_questions: bool,
    search_recency_filter: String,
    top_k: u32,
    stream: bool,
    presence_penalty: u32,
    frequency_penalty: u32,
}

impl PerplexityRequest {
    pub fn new(model: impl ToString, messages: Vec<Message>) -> Self {
        Self {
            model: model.to_string(),
            messages,
            max_tokens: None,
            temperature: 0.2,
            top_p: 0.9,
            search_domain_filter: vec!["perplexity.ai".to_string()],
            return_images: false,
            return_related_questions: false,
            search_recency_filter: "month".to_string(),
            top_k: 0,
            stream: false,
            presence_penalty: 0,
            frequency_penalty: 1,
        }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Delta {
    role: Role,
    content: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Usage {
    prompt_tokens: u64,
    completion_tokens: u64,
    total_tokens: u64,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Choice {
    index: u64,
    finish_reason: String,
    message: Message,
    delta: Delta,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum PerplexityResponse {
    Success {
        id: String,
        model: String,
        object: String,
        created: i64,
        citations: Vec<String>,
        choices: Vec<Choice>,
        usage: Usage,
    },
    Failure {
        detail: Detail,
    },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Detail {
    loc: Vec<String>,
    msg: String,
    r#type: String,
}

#[derive(Deserialize, JsonSchema)]
pub struct ResearchInput {
    /// The question or task for which we want to use internet to find the most
    /// relevant information.
    question: String,
}

#[async_trait::async_trait]
impl ToolCallService for ResearchTool {
    type Input = ResearchInput;
    type Output = String;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        if input.question.is_empty() {
            return Err("Missing parameter: question".to_string());
        }

        let request_body = PerplexityRequest::new(
            self.model.clone(),
            vec![
                Message {
                    role: Role::System,
                    content: "Be precise and concise.".to_string(),
                },
                Message { role: Role::User, content: input.question },
            ],
        );

        // request creation
        let mut headers = HeaderMap::new();
        headers.insert(
            "Authorization",
            format!("Bearer {}", self.api_key).parse().unwrap(),
        );
        headers.insert("Content-Type", "application/json".parse().unwrap());
        let url = reqwest::Url::parse("https://api.perplexity.ai/chat/completions")
            .map_err(|e| e.to_string())?;
        let body = serde_json::to_vec(&request_body).map_err(|e| e.to_string())?;
        let mut request = Request::new(reqwest::Method::POST, url);
        *request.headers_mut() = headers;
        *request.body_mut() = Some(body.into());

        let response_bytes = self
            .client
            .execute(request)
            .await
            .map_err(|e| e.to_string())?;

        let response: PerplexityResponse = serde_json::from_slice(&response_bytes).map_err(|e| e.to_string())?;

        match response {
            PerplexityResponse::Success { choices, .. } => {
                if let Some(choice) = choices.first() {
                    let result = choice.message.content.clone();
                    Ok(result)
                } else {
                    Err("Empty Response returned by researcher.".to_string())
                }
            }
            PerplexityResponse::Failure { detail } => {
                Err(serde_json::to_string(&detail).map_err(|e| e.to_string())?)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::http_client::test_utils::MockHttpIO;
    use std::sync::Arc;

    #[tokio::test]
    async fn test_research_tool_success() {
        let success_response = PerplexityResponse::Success {
            id: "test-id".to_string(),
            model: "test-model".to_string(),
            object: "chat.completion".to_string(),
            created: 1234567890,
            citations: vec![],
            choices: vec![Choice {
                index: 0,
                finish_reason: "stop".to_string(),
                message: Message { role: Role::User, content: "Test response".to_string() },
                delta: Delta { role: Role::User, content: "Test response".to_string() },
            }],
            usage: Usage { prompt_tokens: 10, completion_tokens: 20, total_tokens: 30 },
        };

        let response_bytes = serde_json::to_vec(&success_response).unwrap();
        let mock_client = Arc::new(MockHttpIO::new(vec![response_bytes]));
        let research_tool = ResearchTool::new("test-key", "test-model", mock_client);

        let result = research_tool
            .call(ResearchInput { question: "test question".to_string() })
            .await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "Test response");
    }

    #[tokio::test]
    async fn test_research_tool_failure() {
        let failure_response = PerplexityResponse::Failure {
            detail: Detail {
                loc: vec!["test".to_string()],
                msg: "error message".to_string(),
                r#type: "error".to_string(),
            },
        };

        let response_bytes = serde_json::to_vec(&failure_response).unwrap();
        let mock_client = Arc::new(MockHttpIO::new(vec![response_bytes]));
        let research_tool = ResearchTool::new("test-key", "test-model", mock_client);

        let result = research_tool
            .call(ResearchInput { question: "test question".to_string() })
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_research_tool_empty_question() {
        let mock_client = Arc::new(MockHttpIO::new(vec![]));
        let research_tool = ResearchTool::new("test-key", "test-model", mock_client);

        let result = research_tool
            .call(ResearchInput { question: "".to_string() })
            .await;

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Missing parameter: question");
    }
}
