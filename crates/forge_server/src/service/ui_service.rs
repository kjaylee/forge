use std::sync::Arc;

use forge_provider::{Request, ResultStream};
use tokio_stream::{StreamExt, once};
use crate::Error;

use super::{neo_chat_service::NeoChatService, ChatRequest, ChatResponse, ConversationService};

#[async_trait::async_trait]
pub trait UIServiceTrait: Send + Sync {
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error>;
}

struct Live {
    conversation_service: Arc<dyn ConversationService>,
    neo_chat_service: Arc<dyn NeoChatService>,
}

impl Live {
    pub fn new(
        conversation_service: Arc<dyn ConversationService>,
        neo_chat_service: Arc<dyn NeoChatService>,
    ) -> Self {
        Self {
            conversation_service,
            neo_chat_service,
        }
    }
}

pub struct UIService;

impl UIService {
    pub fn ui_service(
        conversation_service: Arc<dyn ConversationService>,
        neo_chat_service: Arc<dyn NeoChatService>,
    ) -> impl UIServiceTrait {
        Live::new(conversation_service, neo_chat_service)
    }
}

#[async_trait::async_trait]
impl UIServiceTrait for Live {
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error> {
        let mut is_new = false;
       let req = if let Some(conversation_id) = &request.conversation_id {
            self.conversation_service
                .get_conversation(conversation_id.clone())
                .await?
                .context
        } else {
            is_new = true;
            Request::default()
        };

        let conversation = self.conversation_service.set_conversation(&req, None).await?;
        let request = request.conversation_id(conversation.id);

        let stream = self
            .neo_chat_service
            .chat(request.clone(), Request::default())
            .await?;

        let stream = if is_new {
            let id = conversation.id.clone();
            Box::pin(once(Ok(ChatResponse::ConversationStarted {
                conversation_id: id,
            }))
            .chain(stream))
        } else {
            stream
        };

        let conversation_service = self.conversation_service.clone();
        let stream = stream.then(move |message| {
            let conversation_service = conversation_service.clone();
            async move {
                match &message {
                    Ok(ChatResponse::ModifyConversation { id, context }) => {
                        match conversation_service.set_conversation(context, Some(id.clone())).await {
                            Ok(_) => Ok(ChatResponse::Text("".to_string())),
                            Err(e) => Err(e),
                        }
                    }
                    _ => message,
                }
            }
        });

       Ok(Box::pin(stream))
    }
}
