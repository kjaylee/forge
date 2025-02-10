use std::collections::HashMap;
use std::sync::Arc;

use forge_stream::MpscStream;
use serde::{Deserialize, Serialize};

use crate::{
    Agent, AgentId, ChatResponse, Context, ForgeDomain, Orchestrator, SystemContext, Variables,
};

#[derive(Clone, Serialize, Deserialize)]
pub struct Workflow {
    pub agents: Vec<Agent>,
    pub state: HashMap<AgentId, Context>,
    pub variables: Variables,
}

impl Workflow {
    pub fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }

    pub fn get_entries(&self) -> Vec<&Agent> {
        self.agents.iter().filter(|a| a.entry).collect::<Vec<_>>()
    }

    pub fn execute<'a, F: ForgeDomain + 'a>(
        &'a self,
        domain: Arc<F>,
        input: Variables,
        ctx: SystemContext,
    ) -> MpscStream<anyhow::Result<crate::AgentMessage<ChatResponse>>> {
        let workflow = self.clone();
        MpscStream::spawn(move |tx| async move {
            let tx = Arc::new(tx);
            let orch = Orchestrator::new(domain, workflow, ctx, Some(tx.clone()));

            match orch.execute(&input).await {
                Ok(_) => {}
                Err(err) => tx.send(Err(err)).await.unwrap(),
            }
        })
    }
}
