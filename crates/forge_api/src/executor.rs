use std::sync::Arc;

use forge_domain::{AgentMessage, App, ChatRequest, ChatResponse, Orchestrator};
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

            let orch =
                match Orchestrator::try_new(app, request.conversation_id, Some(tx.clone())).await {
                    Ok(orch) => orch,
                    Err(e) => {
                        let _ = tx.send(Err(e)).await;
                        return;
                    }
                };

            if let Err(e) = orch.dispatch(request.event).await {
                let _ = tx.send(Err(e)).await;
            }
        }))
    }
}
