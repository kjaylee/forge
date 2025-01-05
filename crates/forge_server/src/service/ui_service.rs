use std::sync::Arc;

use forge_provider::{Request, ResultStream};
use futures::StreamExt;
use crate::Error;

use super::{neo_chat_service::NeoChatService, ChatRequest, ChatResponse, ConversationService};

#[async_trait::async_trait]
pub trait UIServiceTrait: Send + Sync{
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error>;
}

struct Live{
     conversation_service: Arc<dyn ConversationService>,
     neo_chat_service: Arc<dyn NeoChatService>,
}

impl Live{
    pub fn new(conversation_service: Arc<dyn ConversationService>, neo_chat_service: Arc<dyn NeoChatService>) -> Self{
        Self{
            conversation_service,
            neo_chat_service,
        }
    }   
}

pub struct UIService;

impl UIService{
    pub fn ui_service(conversation_service: Arc<dyn ConversationService>, neo_chat_service: Arc<dyn NeoChatService>) -> impl UIServiceTrait{
        Live::new(conversation_service, neo_chat_service)
    }
    
}



#[async_trait::async_trait]
impl UIServiceTrait for Live{
    async fn chat(&self, request: ChatRequest) -> ResultStream<ChatResponse, Error>{
        let req = if let Some(conversation_id) = &request.conversation_id {
             self.conversation_service.get_conversation(conversation_id.clone()).await?.context
        } else {
            Request::default()
        };
        
        let c = self.conversation_service.set_conversation(&req, None).await?;
        let request = request.conversation_id(c.id);
        let conversation_service = self.conversation_service.clone();
        let stream = self.neo_chat_service.chat(request, Request::default()).await?
            .then(move |message| {
                let conversation_service = conversation_service.clone();
                async move {
                    if let Ok(item) = &message {
                        match item {
                            ChatResponse::ModifyConversation { id, context } => {
                                match conversation_service.set_conversation(context, Some(id.clone())).await {
                                    Ok(_) => Ok(ChatResponse::Text("".to_string())),
                                    Err(e) => Err(e)
                                }
                            }
                            _ => message
                        }
                    } else {
                        message
                    }
                }
            })
            .boxed();
        Ok(stream)
    }
}
