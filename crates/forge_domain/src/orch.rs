use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use anyhow::Context as _;
use async_recursion::async_recursion;
use derive_setters::Setters;
use futures::future::join_all;
use futures::{Stream, StreamExt};
use serde_json::Value;
use tokio::sync::Mutex;

use crate::arena::Arena;
use crate::*;

pub struct AgentMessage<T> {
    pub agent: AgentId,
    pub message: T,
}

#[derive(Setters)]
pub struct Orchestrator {
    provider_svc: Arc<dyn ProviderService>,
    tool_svc: Arc<dyn ToolService>,
    arena: Arena,
    system_context: SystemContext,
    state: Arc<Mutex<HashMap<AgentId, Context>>>,
    sender: Option<tokio::sync::mpsc::Sender<AgentMessage<anyhow::Result<ChatResponse>>>>,
}

struct ChatCompletionResult {
    pub content: String,
    pub tool_calls: Vec<ToolCallFull>,
}

impl Orchestrator {
    pub fn new(provider: Arc<dyn ProviderService>, tool: Arc<dyn ToolService>) -> Self {
        Self {
            provider_svc: provider,
            tool_svc: tool,
            arena: Arena::default(),
            system_context: SystemContext::default(),
            state: Arc::new(Mutex::new(HashMap::new())),
            sender: None,
        }
    }

    pub async fn agent_context(&self, id: &AgentId) -> Option<Context> {
        let guard = self.state.lock().await;
        guard.get(id).cloned()
    }

    pub async fn execute(&self, id: &FlowId, input: &Variables) -> anyhow::Result<Variables> {
        match id {
            FlowId::Agent(id) => self.init_agent(id, input).await,
            FlowId::Workflow(id) => self.init_workflow(id, input).await,
        }
    }

    async fn send_message(
        &self,
        agent_id: &AgentId,
        message: anyhow::Result<ChatResponse>,
    ) -> anyhow::Result<()> {
        if let Some(sender) = &self.sender {
            sender
                .send(AgentMessage { agent: agent_id.clone(), message })
                .await?
        }
        Ok(())
    }

    async fn send(&self, agent_id: &AgentId, message: ChatResponse) -> anyhow::Result<()> {
        self.send_message(agent_id, Ok(message)).await
    }

    async fn send_error(&self, agent_id: &AgentId, error: anyhow::Error) -> anyhow::Result<()> {
        self.send_message(agent_id, Err(error)).await
    }

    fn init_default_tool_definitions(&self) -> Vec<ToolDefinition> {
        self.tool_svc.list()
    }

    fn init_tool_definitions(&self, tools: &[ToolName]) -> Vec<ToolDefinition> {
        let required_tools = tools.iter().collect::<HashSet<_>>();
        let default_tools = self.init_default_tool_definitions();

        default_tools
            .into_iter()
            .filter(|tool| required_tools.contains(&tool.name))
            .collect::<Vec<_>>()
    }

    fn init_agent_context(&self, agent: &Agent, input: &Variables) -> anyhow::Result<Context> {
        let tool_defs = self.init_tool_definitions(&agent.tools);

        let tool_usage_prompt = tool_defs.iter().fold("".to_string(), |acc, tool| {
            format!("{}\n{}", acc, tool.usage_prompt())
        });

        let system_message = agent.system_prompt.render(
            &self
                .system_context
                .clone()
                .tool_information(tool_usage_prompt),
        )?;

        let user_message = ContextMessage::user(agent.user_prompt.render(input)?);

        Ok(Context::default()
            .set_first_system_message(system_message)
            .add_message(user_message)
            .extend_tools(tool_defs))
    }

    async fn collect_messages(
        &self,
        response: impl Stream<Item = std::result::Result<ChatCompletionMessage, anyhow::Error>>,
    ) -> anyhow::Result<ChatCompletionResult> {
        let messages = response
            .collect::<Vec<_>>()
            .await
            .into_iter()
            .collect::<anyhow::Result<Vec<_>>>()?;

        let content = messages
            .iter()
            .flat_map(|m| m.content.iter())
            .map(|content| content.as_str())
            .collect::<Vec<_>>()
            .join("");

        // From Complete (incase streaming is disabled)
        let mut tool_calls: Vec<ToolCallFull> = messages
            .iter()
            .flat_map(|message| message.tool_call.iter())
            .filter_map(|message| message.as_full().cloned())
            .collect::<Vec<_>>();

        // From partial tool calls
        tool_calls.extend(ToolCallFull::try_from_parts(
            &messages
                .iter()
                .filter_map(|message| message.tool_call.first())
                .clone()
                .filter_map(|tool_call| tool_call.as_partial().cloned())
                .collect::<Vec<_>>(),
        )?);

        // From XML
        tool_calls.extend(ToolCallFull::try_from_xml(&content)?);

        Ok(ChatCompletionResult { content, tool_calls })
    }

    fn find_workflow(&self, id: &WorkflowId) -> Option<&Workflow> {
        self.arena.workflows.iter().find(|w| w.id == *id)
    }

    async fn execute_tool(&self, tool_call: &ToolCallFull) -> anyhow::Result<ToolResult> {
        // Check if agent exists

        if let Some(agent) = self.find_agent(&tool_call.name.clone().into()) {
            let input = Variables::from(tool_call.arguments.clone());

            // Tools start fresh with no initial context
            let output = self.init_agent(&agent.id, &input).await;
            into_tool_result(tool_call, output)
                .with_context(|| format!("Failed to serialize output of agent: {}", agent.id))
        } else if let Some(workflow) = self.find_workflow(&tool_call.name.clone().into()) {
            let input = Variables::from(tool_call.arguments.clone());
            let output = self.init_workflow(&workflow.id, &input).await;
            into_tool_result(tool_call, output)
                .with_context(|| format!("Failed to serialize output of workflow: {}", workflow.id))
        } else {
            // TODO: Can check if tool exists
            Ok(self.tool_svc.call(tool_call.clone()).await)
        }
    }

    fn get_workflow(&self, id: &WorkflowId) -> anyhow::Result<&Workflow> {
        Ok(self
            .arena
            .workflows
            .iter()
            .find(|w| w.id == *id)
            .ok_or(Error::WorkflowUndefined(id.clone()))?)
    }

    fn get_agent(&self, id: &AgentId) -> anyhow::Result<&Agent> {
        Ok(self
            .find_agent(id)
            .ok_or(Error::AgentUndefined(id.clone()))?)
    }

    fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.arena.agents.iter().find(|a| a.id == *id)
    }

    #[async_recursion(?Send)]
    async fn execute_transform(
        &self,
        transforms: &[Transform],
        mut context: Context,
    ) -> anyhow::Result<Context> {
        for transform in transforms.iter() {
            match transform {
                Transform::Assistant {
                    agent_id,
                    token_limit,
                    input: input_key,
                    output: output_key,
                } => {
                    let mut summarize = Summarize::new(&mut context, *token_limit);
                    while let Some(mut summary) = summarize.summarize() {
                        let mut input = Variables::default();
                        input.add(input_key, summary.get());

                        let output = self.init_agent(agent_id, &input).await?;
                        let value = output
                            .get(output_key)
                            .ok_or(Error::UndefinedVariable(output_key.to_string()))?;

                        summary.set(serde_json::to_string(&value)?);
                    }
                }
                Transform::User { agent_id, input: input_key, output: output_key } => {
                    if let Some(ContextMessage::ContentMessage(ContentMessage {
                        role: Role::User,
                        content,
                        ..
                    })) = context.messages.last_mut()
                    {
                        let mut input = Variables::default();
                        input.add(input_key, Value::from(content.clone()));

                        let output = self.init_agent(agent_id, &input).await?;
                        let value = output
                            .get(output_key)
                            .ok_or(Error::UndefinedVariable(output_key.to_string()))?;

                        let message = serde_json::to_string(&value)?;

                        content.push_str(&format!("\n<{output_key}>\n{message}\n</{output_key}>"));
                    }
                }
                Transform::Tap { agent_id, input: input_key } => {
                    let mut input = Variables::default();
                    input.add(input_key, context.to_text());

                    // NOTE: Tap transformers will not modify the context
                    self.init_agent(agent_id, &input).await?;
                }
            }
        }

        Ok(context)
    }

    async fn init_agent(&self, agent: &AgentId, input: &Variables) -> anyhow::Result<Variables> {
        let agent = self.get_agent(agent)?;

        let mut context = if agent.ephemeral {
            self.init_agent_context(agent, input)?
        } else {
            self.state
                .lock()
                .await
                .get(&agent.id)
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| self.init_agent_context(agent, input))?
        };

        let content = agent.user_prompt.render(input)?;
        let output = Variables::default();
        context = context.add_message(ContextMessage::user(content));

        loop {
            context = self.execute_transform(&agent.transforms, context).await?;

            let response = self
                .provider_svc
                .chat(&agent.model, context.clone())
                .await?;
            let ChatCompletionResult { tool_calls, content } =
                self.collect_messages(response).await?;
            let tool_call_count = tool_calls.len();

            let tool_results = join_all(
                tool_calls
                    .iter()
                    .map(|tool_call| self.execute_tool(tool_call)),
            )
            .await
            .into_iter()
            .collect::<anyhow::Result<Vec<_>>>()?;

            context = context
                .add_message(ContextMessage::assistant(content, Some(tool_calls)))
                .add_tool_results(tool_results);

            if !agent.ephemeral {
                self.state
                    .lock()
                    .await
                    .insert(agent.id.clone(), context.clone());
            }

            if tool_call_count == 0 {
                return Ok(output);
            }
        }
    }

    async fn init_flow(
        &self,
        flow_id: &FlowId,
        input: &Variables,
        workflow: &Workflow,
    ) -> anyhow::Result<Variables> {
        match flow_id {
            FlowId::Agent(agent_id) => {
                let variables = self.init_agent(agent_id, input).await?;
                let flows = workflow
                    .handovers
                    .get(&agent_id.clone().into())
                    .ok_or(Error::AgentUndefined(agent_id.clone()))?;

                join_all(
                    flows
                        .iter()
                        .map(|handovers| self.init_flow(&handovers.flow_id, &variables, workflow)),
                )
                .await
                .into_iter()
                .collect::<anyhow::Result<Vec<_>>>()
                .map(Variables::from)
            }
            FlowId::Workflow(id) => self.init_workflow(id, input).await,
        }
    }

    #[async_recursion(?Send)]
    async fn init_workflow(&self, id: &WorkflowId, input: &Variables) -> anyhow::Result<Variables> {
        let workflow = self.get_workflow(id)?;
        self.init_flow(&workflow.head_flow, input, workflow).await
    }
}

fn into_tool_result(
    tool_call: &ToolCallFull,
    output: anyhow::Result<Variables>,
) -> anyhow::Result<ToolResult> {
    match output {
        Ok(output) => {
            let output = serde_json::to_string(&output)?;
            Ok(ToolResult::from(tool_call.clone()).success(output))
        }
        Err(error) => Ok(ToolResult::from(tool_call.clone()).failure(error.to_string())),
    }
}
