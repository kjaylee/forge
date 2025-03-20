use std::sync::Arc;

use forge_domain::{
    AgentMessage, App, ChatRequest, ChatResponse, ConversationService, Orchestrator,
};
use forge_stream::MpscStream;

pub struct ForgeExecutorService<F> {
    app: Arc<F>,
}
impl<F: App> ForgeExecutorService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { app: infra }
    }
}

impl<F: App> ForgeExecutorService<F> {
    pub async fn chat(
        &self,
        request: ChatRequest,
    ) -> anyhow::Result<MpscStream<anyhow::Result<AgentMessage<ChatResponse>>>> {
        let app = self.app.clone();

        Ok(MpscStream::spawn(move |tx| async move {
            let tx = Arc::new(tx);
            let mut conversation = app
                .conversation_service()
                .get(&request.conversation_id)
                .await
                .unwrap_or_default()
                .expect("conversation for the request should've been created");
            conversation.state.values_mut().for_each(|state| {
                // since this is a new request, we clear the queue and start fresh with new events.
                state.queue.clear();
            });

            let orch = Orchestrator::new(app, conversation, Some(tx.clone()));

            match orch.dispatch(request.event).await {
                Ok(_) => {}
                Err(err) => tx.send(Err(err)).await.unwrap(),
            }
        }))
    }
}
