use std::sync::Arc;

use forge_domain::{Context, ResultStream};
use tokio_stream::{once, StreamExt};
use tracing::info;

use super::{ChatRequest, ChatResponse, ChatService, ConversationService};
use crate::{Error, Service};

#[async_trait::async_trait]
pub trait UIService: Send + Sync {
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error>;
}

struct Live {
    conversation_service: Arc<dyn ConversationService>,
    chat_service: Arc<dyn ChatService>,
    title_service: Arc<dyn ChatService>,
}

impl Live {
    fn new(
        conversation_service: Arc<dyn ConversationService>,
        chat_service: Arc<dyn ChatService>,
        title_service: Arc<dyn ChatService>,
    ) -> Self {
        Self { conversation_service, chat_service, title_service }
    }
}

impl Service {
    pub fn ui_service(
        conversation_service: Arc<dyn ConversationService>,
        neo_chat_service: Arc<dyn ChatService>,
        title_service: Arc<dyn ChatService>,
    ) -> impl UIService {
        Live::new(conversation_service, neo_chat_service, title_service)
    }
}

#[async_trait::async_trait]
impl UIService for Live {
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error> {
        let (conversation, is_new) = if let Some(conversation_id) = &request.conversation_id {
            let context = self
                .conversation_service
                .get_conversation(*conversation_id)
                .await?;
            (context, false)
        } else {
            let conversation = self
                .conversation_service
                .set_conversation(&Context::default(), None)
                .await?;
            (conversation, true)
        };

        info!("Job {} started", conversation.id.as_uuid());
        let request = request.conversation_id(conversation.id);

        let mut stream = self
            .chat_service
            .chat(request.clone(), conversation.context)
            .await?;

        if is_new {
            // since conversation is new, we've to generate the title for conversation.
            let title = self
                .title_service
                .chat(request.clone(), Context::default())
                .await?
                .filter_map(|msg| match msg {
                    Ok(ChatResponse::Text(text)) => Some(text),
                    _ => None,
                })
                .collect::<String>()
                .await;
            let id = conversation.id;
            stream = Box::pin(
                once(Ok(ChatResponse::ConversationStarted {
                    conversation_id: id,
                    title,
                }))
                .chain(stream),
            );
        }

        let conversation_service = self.conversation_service.clone();
        let stream = stream
            .then(move |message| {
                let conversation_service = conversation_service.clone();
                async move {
                    match &message {
                        Ok(ChatResponse::ConversationStarted { conversation_id, title }) => {
                            conversation_service
                                .set_conversation_title(conversation_id, title.to_owned())
                                .await?;
                            message
                        }
                        Ok(ChatResponse::ModifyContext(context)) => {
                            conversation_service
                                .set_conversation(context, request.conversation_id)
                                .await?;
                            message
                        }
                        _ => message,
                    }
                }
            })
            .filter(|message| !matches!(message, Ok(ChatResponse::ModifyContext { .. })));

        Ok(Box::pin(stream))
    }
}

#[cfg(test)]
mod tests {

    use forge_domain::ModelId;

    use super::super::conversation_service::tests::TestStorage;
    use super::*;

    struct TestTitleService;

    #[async_trait::async_trait]
    impl ChatService for TestTitleService {
        async fn chat(&self, _: ChatRequest, _: Context) -> ResultStream<ChatResponse, Error> {
            Ok(Box::pin(once(Ok(ChatResponse::Text(
                "test title generated".to_string(),
            )))))
        }
    }

    #[async_trait::async_trait]
    impl ChatService for TestStorage {
        async fn chat(&self, _: ChatRequest, _: Context) -> ResultStream<ChatResponse, Error> {
            Ok(Box::pin(once(Ok(ChatResponse::Text(
                "test message".to_string(),
            )))))
        }
    }

    impl Default for ChatRequest {
        fn default() -> Self {
            Self {
                content: "test".to_string(),
                model: ModelId::default(),
                conversation_id: None,
            }
        }
    }

    #[tokio::test]
    async fn test_chat_new_conversation() {
        let storage = Arc::new(TestStorage);
        let conversation_service = Arc::new(TestStorage::in_memory().unwrap());
        let service = Service::ui_service(
            conversation_service.clone(),
            storage.clone(),
            Arc::new(TestTitleService),
        );
        let request = ChatRequest::default();

        let mut responses = service.chat(request).await.unwrap();

        if let Some(Ok(ChatResponse::ConversationStarted { title, .. })) = responses.next().await {
            assert_eq!(title, "test title generated");
        } else {
            panic!("Expected ConversationStarted response");
        }

        if let Some(Ok(ChatResponse::Text(content))) = responses.next().await {
            assert_eq!(content, "test message");
        } else {
            panic!("Expected Text response");
        }
    }

    #[tokio::test]
    async fn test_chat_existing_conversation() {
        let storage = Arc::new(TestStorage);
        let conversation_service = Arc::new(TestStorage::in_memory().unwrap());
        let service = Service::ui_service(
            conversation_service.clone(),
            storage.clone(),
            Arc::new(TestTitleService),
        );

        let conversation = conversation_service
            .set_conversation(&Context::default(), None)
            .await
            .unwrap();

        let request = ChatRequest::default().conversation_id(conversation.id);
        let mut responses = service.chat(request).await.unwrap();

        if let Some(Ok(ChatResponse::Text(content))) = responses.next().await {
            assert_eq!(content, "test message");
        } else {
            panic!("Expected Text response");
        }
    }
}
