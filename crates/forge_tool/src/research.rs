use forge_domain::{NamedTool, ToolCallService, ToolDescription};
use forge_tool_macros::ToolDescription;
use reqwest::Client;
use schemars::JsonSchema;
use serde::Deserialize;

/// Request to research about a topic. The tool will use the internet to find
/// the most relevant information about the topic and return the information in
/// a readable format.
#[derive(Clone, Debug, ToolDescription)]
pub struct ResearchTool {
    api_key: String,
    model: String,
    client: Client,
}

impl ResearchTool {
    pub fn new(api_key: impl ToString, model: impl ToString) -> Self {
        Self {
            api_key: api_key.to_string(),
            model: model.to_string(),
            client: Client::new(),
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
enum Role {
    System,
    User,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct Message {
    role: Role,
    content: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct PerplexityRequest {
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

    pub fn json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct Delta {
    role: Role,
    content: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct Usage {
    prompt_tokens: u64,
    completion_tokens: u64,
    total_tokens: u64,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct Choice {
    index: u64,
    finish_reason: String,
    message: Message,
    delta: Delta,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
enum PerplexityResponse {
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
struct Detail {
    loc: Vec<String>,
    msg: String,
    r#type: String,
}

#[derive(Deserialize, JsonSchema)]
pub struct ResearchInput {
    /// The question or task for which we want to use internet to find the most relevant information.
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
        )
        .json()
        .map_err(|e| e.to_string())?;

        let response = self
            .client
            .post("https://api.perplexity.ai/chat/completions")
            .header("Authorization", format!("Bearer {}", self.api_key))
            .header("Content-Type", "application/json")
            .body(request_body)
            .send()
            .await
            .map_err(|e| e.to_string())?;

        let response: PerplexityResponse = response.json().await.map_err(|e| e.to_string())?;
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

    #[test]
    fn test_deserialize_perplexity_request() {
        let request_body = PerplexityRequest::new(
            "llama-3.1-sonar-small-128k-online".to_string(),
            vec![
                Message {
                    role: Role::System,
                    content: "Be precise and concise.".to_string(),
                },
                Message {
                    role: Role::User,
                    content: "How many stars are there in our galaxy?".to_string(),
                },
            ],
        );

        println!("{}", serde_json::to_string_pretty(&request_body).unwrap());
    }
}
