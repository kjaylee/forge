use std::sync::Arc;

use forge_domain::{Context, ResultStream};
use tokio_stream::{once, StreamExt};

use super::chat_service::ChatService;
use super::{ChatRequest, ChatResponse, ConversationService};
use crate::Error;

#[async_trait::async_trait]
pub trait UIServiceTrait: Send + Sync {
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error>;
}

struct Live {
    conversation_service: Arc<dyn ConversationService>,
    chat_service: Arc<dyn ChatService>,
}

impl Live {
    pub fn new(
        conversation_service: Arc<dyn ConversationService>,
        chat_service: Arc<dyn ChatService>,
    ) -> Self {
        Self { conversation_service, chat_service }
    }
}

pub struct UIService;

impl UIService {
    pub fn ui_service(
        conversation_service: Arc<dyn ConversationService>,
        neo_chat_service: Arc<dyn ChatService>,
    ) -> impl UIServiceTrait {
        Live::new(conversation_service, neo_chat_service)
    }
}

#[async_trait::async_trait]
impl UIServiceTrait for Live {
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

        let request = request.conversation_id(conversation.id);

        let mut stream = self
            .chat_service
            .chat(request.clone(), conversation.context)
            .await?;

        if is_new {
            let id = conversation.id;
            stream = Box::pin(
                once(Ok(ChatResponse::ConversationStarted {
                    conversation_id: id,
                }))
                .chain(stream),
            );
        }

        let conversation_service = self.conversation_service.clone();
        let stream = stream
            .then(move |message| {
                let conversation_service = conversation_service.clone();
                async move {
                    if let Ok(ChatResponse::ModifyConversation { id, context }) = &message {
                        conversation_service
                            .set_conversation(context, Some(*id))
                            .await?;
                        message
                    } else {
                        message
                    }
                }
            })
            .filter(|message| !matches!(message, Ok(ChatResponse::ModifyConversation { .. })));

        Ok(Box::pin(stream))
    }
}
