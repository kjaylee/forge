use std::sync::Arc;

use forge_domain::{Context, ContextMessage, ResultStream};
use forge_provider::ProviderService;
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::StreamExt;

use super::system_prompt_service::SystemPromptService;
use super::user_prompt_service::UserPromptService;
use super::{ChatRequest, ChatResponse, ChatService, Service};
use crate::{Error, Result};

impl Service {
    pub fn title_service(
        provider: Arc<dyn ProviderService>,
        system_prompt: Arc<dyn SystemPromptService>,
        user_prompt: Arc<dyn UserPromptService>,
    ) -> impl ChatService {
        Live::new(provider, system_prompt, user_prompt)
    }
}

#[derive(Clone)]
struct Live {
    provider: Arc<dyn ProviderService>,
    system_prompt: Arc<dyn SystemPromptService>,
    user_prompt: Arc<dyn UserPromptService>,
}

impl Live {
    fn new(
        provider: Arc<dyn ProviderService>,
        system_prompt: Arc<dyn SystemPromptService>,
        user_prompt: Arc<dyn UserPromptService>,
    ) -> Self {
        Self { provider, system_prompt, user_prompt }
    }

    /// Executes the chat workflow until the task is complete.
    async fn execute(
        &self,
        request: Context,
        tx: tokio::sync::mpsc::Sender<Result<ChatResponse>>,
    ) -> Result<()> {
        let mut assistant_response = String::new();
        let mut response = self.provider.chat(request.clone()).await?;

        while let Some(chunk) = response.next().await {
            let message = chunk?;
            if let Some(ref content) = message.content {
                if !content.is_empty() {
                    assistant_response.push_str(content.as_str());
                }
            }
        }

        tx.send(Ok(ChatResponse::Text(assistant_response)))
            .await
            .unwrap();
        Ok(())
    }
}

#[async_trait::async_trait]
impl ChatService for Live {
    async fn chat(&self, chat: ChatRequest, request: Context) -> ResultStream<ChatResponse, Error> {
        let system_prompt = self.system_prompt.get_system_prompt(&chat.model).await?;
        let user_prompt = self.user_prompt.get_user_prompt(&chat.content).await?;
        let (tx, rx) = tokio::sync::mpsc::channel(1);

        let request = request
            .set_system_message(system_prompt)
            .add_message(ContextMessage::user(user_prompt))
            .model(chat.model);

        let that = self.clone();

        tokio::spawn(async move {
            // TODO: simplify this match.
            match that.execute(request, tx.clone()).await {
                Ok(_) => {}
                Err(e) => tx.send(Err(e)).await.unwrap(),
            };

            tx.send(Ok(ChatResponse::Complete)).await.unwrap();

            drop(tx);
        });

        Ok(Box::pin(ReceiverStream::new(rx)))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::vec;

    use derive_setters::Setters;
    use forge_domain::{ChatCompletionMessage, Context, FinishReason};
    use pretty_assertions::assert_eq;
    use tokio_stream::StreamExt;

    use super::{ChatRequest, Live};
    use crate::service::chat_service::ChatService;
    use crate::service::tests::{TestProvider, TestSystemPrompt};
    use crate::service::title_user_prompt_service::tests::TestUserPrompt;
    use crate::service::{ChatResponse, ConversationId};

    #[derive(Default, Setters)]
    #[setters(into, strip_option)]
    struct Fixture {
        assistant_responses: Vec<Vec<ChatCompletionMessage>>,
        system_prompt: String,
    }

    impl Fixture {
        pub async fn run(&self, request: ChatRequest) -> Vec<ChatResponse> {
            let provider =
                Arc::new(TestProvider::default().with_messages(self.assistant_responses.clone()));
            let system_prompt_message = if self.system_prompt.is_empty() {
                "Given a task, generate a title for the task."
            } else {
                self.system_prompt.as_str()
            };
            let system_prompt = Arc::new(TestSystemPrompt::new(system_prompt_message));
            let user_prompt = Arc::new(TestUserPrompt);
            let chat = Live::new(provider.clone(), system_prompt.clone(), user_prompt.clone());

            chat.chat(request, Context::default())
                .await
                .unwrap()
                .collect::<Vec<_>>()
                .await
                .into_iter()
                .map(|message| message.unwrap())
                .collect::<Vec<_>>()
        }
    }

    #[tokio::test]
    async fn test_title_generation() {
        let mock_llm_responses = vec![vec![ChatCompletionMessage::default()
            .content_part("Fibonacci Sequence in Rust")
            .finish_reason(FinishReason::Stop)]];

        let actual = Fixture::default()
            .assistant_responses(mock_llm_responses)
            .run(
                ChatRequest::new("write an rust program to generate an fibo seq.")
                    .conversation_id(ConversationId::new("5af97419-0277-410a-8ca6-0e2a252152c5")),
            )
            .await;

        let expected = vec![
            ChatResponse::Text("Fibonacci Sequence in Rust".to_string()),
            ChatResponse::Complete,
        ];
        assert_eq!(actual, expected);
    }
}
