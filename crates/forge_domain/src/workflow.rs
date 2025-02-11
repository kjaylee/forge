use std::collections::HashMap;
use std::sync::Arc;

use forge_stream::MpscStream;
use serde::{Deserialize, Serialize};

use crate::{Agent, AgentId, App, ChatResponse, Context, Orchestrator, SystemContext, Variables};

#[derive(Clone, Serialize, Deserialize)]
pub struct Workflow {
    pub agents: Vec<Agent>,
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub state: HashMap<AgentId, Context>,
    #[serde(skip_serializing_if = "Variables::is_empty")]
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

    pub fn entries(&self) -> Vec<Agent> {
        self.agents
            .iter()
            .filter(|a| a.entry)
            .cloned()
            .collect::<Vec<_>>()
    }

    pub fn execute<'a, F: App + 'a>(
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
