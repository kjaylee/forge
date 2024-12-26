use async_openai::{
    config::OpenAIConfig,
    error::OpenAIError,
    types::{
        ChatCompletionRequestMessage, ChatCompletionRequestSystemMessage,
        ChatCompletionRequestUserMessage, ChatCompletionRequestSystemMessageContent,
        ChatCompletionRequestUserMessageContent, CreateChatCompletionRequest,
        ChatCompletionTool, ChatCompletionToolType, FunctionObject, 
        ChatCompletionToolChoiceOption, ChatCompletionNamedToolChoice,
        FunctionName, ResponseFormat, Stop, FinishReason,
    },
    Client,
};
use tokio_stream::StreamExt;
use tracing::info;

use super::chat_request::{ChatRequest, ToolChoice};
use super::chat_response::{
    ChatResponse, Choice, ResponseMessage, ToolCall, FunctionCall,
};
use super::model_response::{ListModelResponse, Model};
use crate::error::Result;
use crate::provider::{InnerProvider, Provider};
use crate::{Error, ProviderError, Request, Response, ResultStream, UseId};
use forge_tool::ToolName;

const PROVIDER_NAME: &str = "Open Router";

#[derive(Clone)]
struct OpenRouter {
    client: Client<OpenAIConfig>,
    http_client: reqwest::Client,
    base_url: String,
}

impl OpenRouter {
    fn new(api_key: String, base_url: Option<String>) -> Self {
        let mut headers = reqwest::header::HeaderMap::new();
        // OpenRouter required headers
        headers.insert(
            "Authorization",
            reqwest::header::HeaderValue::from_str(&format!("Bearer {}", api_key)).unwrap(),
        );
        headers.insert(
            "HTTP-Referer",
            reqwest::header::HeaderValue::from_static("code-forge"),
        );
        headers.insert(
            "X-Title",
            reqwest::header::HeaderValue::from_static("Code Forge"),
        );
        // Additional OpenRouter headers
        headers.insert(
            "User-Agent",
            reqwest::header::HeaderValue::from_static("Code Forge/1.0.0"),
        );

        let http_client = reqwest::Client::builder()
            .default_headers(headers)
            .build()
            .unwrap();

        let base_url = base_url.unwrap_or_else(|| "https://openrouter.ai/api/v1".to_string());
        let config = OpenAIConfig::new()
            .with_api_base(&base_url)
            .with_api_key(api_key.clone());

        Self {
            client: Client::with_config(config)
                .with_http_client(http_client.clone()),
            http_client,
            base_url: base_url,
        }
    }
}

impl TryFrom<ChatRequest> for CreateChatCompletionRequest {
    type Error = Error;

    fn try_from(req: ChatRequest) -> Result<Self> {
        let mut request = CreateChatCompletionRequest::default();
        
        if let Some(messages) = req.messages {
            let messages = messages
                .into_iter()
                .map(|msg| match msg.role.as_str() {
                    "system" => ChatCompletionRequestMessage::System(ChatCompletionRequestSystemMessage {
                        content: ChatCompletionRequestSystemMessageContent::Text(msg.content),
                        name: msg.name,
                    }),
                    _ => ChatCompletionRequestMessage::User(ChatCompletionRequestUserMessage {
                        content: ChatCompletionRequestUserMessageContent::Text(msg.content),
                        name: msg.name,
                    }),
                })
                .collect::<Vec<_>>();
            request.messages = messages;
        }

        // OpenRouter expects model IDs without quotes
        request.model = req.model.0.trim_matches('"').to_string();
        
        // Map all available fields from ChatRequest to CreateChatCompletionRequest
        request.stream = req.stream;
        request.max_tokens = req.max_tokens;
        request.temperature = req.temperature;
        request.top_p = req.top_p;
        request.frequency_penalty = req.frequency_penalty;
        request.presence_penalty = req.presence_penalty;
        
        // Additional fields
        if let Some(tools) = req.tools {
            request.tools = Some(tools.into_iter().map(|tool| ChatCompletionTool {
                r#type: ChatCompletionToolType::Function,
                function: FunctionObject {
                    name: tool.function.name,
                    description: tool.function.description,
                    parameters: Some(tool.function.parameters),
                    strict: None,
                },
            }).collect());
        }
        
        if let Some(tool_choice) = req.tool_choice {
            request.tool_choice = Some(match tool_choice {
                ToolChoice::None => ChatCompletionToolChoiceOption::None,
                ToolChoice::Auto => ChatCompletionToolChoiceOption::Auto,
                ToolChoice::Function { name } => ChatCompletionToolChoiceOption::Named(
                    ChatCompletionNamedToolChoice {
                        r#type: ChatCompletionToolType::Function,
                        function: FunctionName { name },
                    }
                ),
            });
        }
        
        if req.response_format.is_some() {
            request.response_format = Some(ResponseFormat::JsonObject);
        }
        
        request.stop = req.stop.map(|stops| {
            if stops.len() == 1 {
                Stop::String(stops[0].clone())
            } else {
                Stop::StringArray(stops)
            }
        });
        
        request.seed = req.seed.map(|s| s as i64);
        request.logit_bias = req.logit_bias.map(|bias| {
            bias.into_iter()
                .map(|(k, v)| (k.to_string(), serde_json::Value::Number(serde_json::Number::from_f64(v as f64).unwrap())))
                .collect()
        });
        
        Ok(request)
    }
}

impl From<OpenAIError> for Error {
    fn from(err: OpenAIError) -> Self {
        match err {
            OpenAIError::ApiError(e) => {
                let error_msg = e.message.to_lowercase();
                if error_msg.contains("401") || error_msg.contains("unauthorized") || error_msg.contains("invalid api key") {
                    Error::Provider {
                        provider: PROVIDER_NAME.to_string(),
                        error: ProviderError::AuthenticationError,
                    }
                } else {
                    Error::Provider {
                        provider: PROVIDER_NAME.to_string(),
                        error: ProviderError::UpstreamError(serde_json::json!({
                            "error": e.message,
                            "type": e.r#type,
                            "code": e.code
                        })),
                    }
                }
            }
            _ => Error::Provider {
                provider: PROVIDER_NAME.to_string(),
                error: ProviderError::UpstreamError(serde_json::json!({ "error": err.to_string() })),
            },
        }
    }
}

#[async_trait::async_trait]
impl InnerProvider for OpenRouter {
    type Request = crate::model::Request;
    type Response = crate::model::Response;
    type Error = Error;

    async fn chat(&self, request: Self::Request) -> ResultStream<Self::Response, Self::Error> {
        let mut request = ChatRequest::from(request);
        request.stream = Some(true);
        
        let chat_request = CreateChatCompletionRequest::try_from(request)?;
        
        let mut stream = self.client.chat().create_stream(chat_request).await?;

        // Create a stream that handles function calls properly
        let stream = Box::pin(async_stream::stream! {
            let mut fn_name = String::new();
            let mut fn_args = String::new();
            let mut tool_call_id = String::new();

            while let Some(result) = stream.next().await {
                match result {
                    Ok(response) => {
                        
                        let choices = response.choices.clone();
                        
                        for chat_choice in choices {
                            // Handle regular content and tool calls
                            if let Some(content) = chat_choice.delta.content {
                                let chat_response = ChatResponse {
                                    id: response.id.clone(),
                                    object: "chat.completion.chunk".to_string(),
                                    created: response.created as u64,
                                    model: response.model.clone(),
                                    system_fingerprint: response.system_fingerprint.clone(),
                                    provider: None,
                                    usage: None,
                                    choices: vec![Choice::Streaming {
                                        delta: ResponseMessage {
                                            role: Some("assistant".to_string()),
                                            content: Some(content),
                                            tool_calls: None,
                                            refusal: None,
                                        },
                                        finish_reason: None,
                                        error: None,
                                    }],
                                };

                                if let Ok(response) = crate::Response::try_from(chat_response) {
                                    yield Ok(response);
                                }
                            }

                            // Handle tool calls
                            if let Some(tool_calls) = chat_choice.delta.tool_calls {
                                for tool_call in tool_calls {
                                    if let Some(id) = tool_call.id {
                                        tool_call_id = id;
                                    }
                                    if let Some(function) = tool_call.function {
                                        if let Some(name) = function.name {
                                            fn_name = name;
                                        }
                                        if let Some(args) = function.arguments {
                                            fn_args.push_str(&args);
                                        }
                                    }
                                }
                            }

                            // Handle finish reason
                            if let Some(finish_reason) = chat_choice.finish_reason {
                                if matches!(finish_reason, FinishReason::ToolCalls) && !fn_name.is_empty() {
                                    let chat_response = ChatResponse {
                                        id: response.id.clone(),
                                        object: "chat.completion.chunk".to_string(),
                                        created: response.created as u64,
                                        model: response.model.clone(),
                                        system_fingerprint: response.system_fingerprint.clone(),
                                        provider: None,
                                        usage: None,
                                        choices: vec![Choice::Streaming {
                                            delta: ResponseMessage {
                                                role: Some("assistant".to_string()),
                                                content: None,
                                                tool_calls: Some(vec![ToolCall {
                                                id: Some(UseId(tool_call_id.clone())),
                                                r#type: "function".to_string(),
                                                function: FunctionCall {
                                                    name: Some(ToolName(fn_name.clone())),
                                                    arguments: fn_args.clone(),
                                                    },
                                                }]),
                                                refusal: None,
                                            },
                                            finish_reason: Some("tool_calls".to_string()),
                                            error: None,
                                        }],
                                    };

                                    if let Ok(response) = crate::Response::try_from(chat_response) {
                                        yield Ok(response);
                                    }

                                    // Reset state
                                    fn_name.clear();
                                    fn_args.clear();
                                    tool_call_id.clear();
                                }
                            }
                        }
                    }
                    Err(err) => {
                        info!("Stream error: {}", err);
                        yield Err(Error::from(err));
                    }
                }
            }
        });

        Ok(stream)
    }

    async fn models(&self) -> Result<Vec<crate::Model>> {
        let response = self.http_client
            .get(format!("{}/models", self.base_url))
            .send()
            .await?;
            
        let model_response = response.json::<ListModelResponse>().await?;
        
        let models = model_response.data.into_iter()
            .map(|model| crate::Model::from(model))
            .collect::<Vec<_>>();
            
        info!("Successfully retrieved {} models", models.len());
        Ok(models)
    }
}

impl Provider<Request, Response, Error> {
    pub fn open_router(api_key: String, base_url: Option<String>) -> Self {
        Provider::new(OpenRouter::new(api_key, base_url))
    }
}

impl From<Model> for crate::Model {
    fn from(value: Model) -> Self {
        crate::Model {
            id: value.id,
            name: value.name,
            description: value.description,
        }
    }
}
