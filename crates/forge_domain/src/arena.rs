use std::sync::Arc;

use futures::future::join_all;
use futures::Stream;

use crate::{
    Agent, AgentId, ChatCompletionMessage, Context, ContextMessage, FlowId, ProviderService, Schema, ToolCallFull, ToolName, ToolResult,
    Transform, Variables, Workflow, WorkflowId,
};

#[async_trait::async_trait]
pub trait AgentExecutor {
    async fn execute(&self, agent: &Agent) -> anyhow::Result<Variables>;
}

pub struct Arena {
    pub agents: Vec<Agent>,
    pub workflows: Vec<Workflow>,
    pub tools: Vec<SmartTool<Variables>>,
}

impl Arena {
    pub fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }
}

pub struct SmartTool<S> {
    pub name: ToolName,
    pub description: String,
    pub run: FlowId,
    pub input: Schema<S>,
}

pub enum FlowContext {
    Agent(Agent),
    Workflow(Workflow),
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Agent not found in the arena: {0}")]
    AgentUndefined(AgentId),

    #[error("Workflow not found in the arena: {0}")]
    WorkflowUndefined(WorkflowId),
}

pub struct HandoverValue<T> {
    pub from: FlowId,
    pub to: FlowId,
    pub value: T,
}

pub type Result<A> = std::result::Result<A, Error>;

pub struct WorkflowEngine {
    arena: Arena,
    provider: Arc<dyn ProviderService>,
}

impl WorkflowEngine {
    pub fn new(provider: Arc<dyn ProviderService>, arena: Arena) -> Self {
        Self { arena, provider }
    }

    pub async fn execute(&self, id: &FlowId, input: &Variables) -> anyhow::Result<()> {
        match id {
            FlowId::Agent(id) => {
                let id = self
                    .arena
                    .agents
                    .iter()
                    .find(|a| &a.id == id)
                    .ok_or(Error::AgentUndefined(id.clone()))?;

                self.init_agent(id, input).await?;
                Ok(())
            }
            FlowId::Workflow(id) => {
                let id = self
                    .arena
                    .workflows
                    .iter()
                    .find(|w| &w.id == id)
                    .ok_or(Error::WorkflowUndefined(id.clone()))?;

                self.init_workflow(id, input).await
            }
        }
    }

    fn agent_context(&self, agent: &Agent) -> Context {
        todo!()
    }

    async fn collect_content(
        &self,
        response: &impl Stream<Item = std::result::Result<ChatCompletionMessage, anyhow::Error>>,
    ) -> String {
        todo!()
    }

    async fn collect_tool_calls(
        &self,
        response: &impl Stream<Item = std::result::Result<ChatCompletionMessage, anyhow::Error>>,
        variables: &mut Variables,
    ) -> Vec<ToolCallFull> {
        todo!()
    }

    async fn execute_tool(&self, tool_call: &ToolCallFull) -> ToolResult {
        todo!()
    }

    async fn execute_transform(
        &self,
        transform: &Vec<Transform>,
        context: Context,
    ) -> anyhow::Result<Context> {
        todo!()
    }

    async fn init_agent(&self, agent: &Agent, input: &Variables) -> anyhow::Result<Variables> {
        let mut context = self.agent_context(agent);
        let content = agent.user_prompt.render(input);
        let mut output = Variables::default();
        context = context.add_message(ContextMessage::user(content));

        loop {
            context = self.execute_transform(&agent.transforms, context).await?;

            let response = self.provider.chat(&agent.model, context.clone()).await?;
            let tool_calls = self.collect_tool_calls(&response, &mut output).await;

            if tool_calls.is_empty() {
                return Ok(output);
            }

            let content = self.collect_content(&response).await;

            let tool_results = join_all(
                tool_calls
                    .iter()
                    .map(|tool_call| self.execute_tool(tool_call)),
            )
            .await;

            context = context
                .add_message(ContextMessage::assistant(content, Some(tool_calls)))
                .add_tool_results(tool_results);
        }
    }

    async fn init_workflow_with(
        &self,
        workflow: &Workflow,
        input: &Variables,
        flow_id: &FlowId,
    ) -> anyhow::Result<()> {
        match flow_id {
            FlowId::Agent(agent_id) => {
                let agent = self
                    .arena
                    .agents
                    .iter()
                    .find(|a| &a.id == agent_id)
                    .ok_or(Error::AgentUndefined(agent_id.clone()))?;

                let variables = self.init_agent(agent, input).await?;
                let flows = workflow
                    .handovers
                    .get(&agent_id.clone().into())
                    .ok_or(Error::AgentUndefined(agent_id.clone()))?;

                join_all(
                    flows
                        .iter()
                        .map(|flow_id| self.init_workflow_with(workflow, &variables, flow_id)),
                )
                .await
                .into_iter()
                .collect::<anyhow::Result<Vec<_>>>()?;

                Ok(())
            }
            FlowId::Workflow(id) => {
                let id = self
                    .arena
                    .workflows
                    .iter()
                    .find(|w| &w.id == id)
                    .ok_or(Error::WorkflowUndefined(id.clone()))?;

                self.init_workflow(id, input).await
            }
        }
    }

    async fn init_workflow(&self, workflow: &Workflow, input: &Variables) -> anyhow::Result<()> {
        join_all(
            workflow
                .head_flow()
                .iter()
                .map(|flow_id| self.init_workflow_with(workflow, input, flow_id)),
        )
        .await
        .into_iter()
        .collect::<anyhow::Result<()>>()
    }
}
