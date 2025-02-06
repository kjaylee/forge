use std::collections::HashSet;
use std::sync::Arc;
use parking_lot::RwLock;

use anyhow::Context as _;
use async_recursion::async_recursion;
use futures::future::join_all;
use futures::Stream;
use serde_json::Value;

use crate::arena::{Arena, SmartTool};
use crate::{
    Agent, AgentId, ChatCompletionMessage, ChatResponse, ContentMessage, Context, ContextMessage, Error, FlowId,
    ProviderService, Role, Summarize, SystemContext, ToolCall, ToolCallFull, ToolDefinition,
    ToolName, ToolResult, ToolService, Transform, Variables, Workflow, WorkflowId,
};

#[derive(Clone)]
pub struct Orchestrator {
    arena: Arena,
    system_context: SystemContext,
    provider: Arc<dyn ProviderService>,
    tool: Arc<dyn ToolService>,
    response_tx: Option<tokio::sync::mpsc::UnboundedSender<ChatResponse>>,
    workflow_context: Arc<RwLock<Context>>,
}

impl Orchestrator {
    pub fn new(
        provider: Arc<dyn ProviderService>,
        tool: Arc<dyn ToolService>,
        arena: Arena,
        system_context: SystemContext,
    ) -> Self {
        Self { 
            arena, 
            provider, 
            system_context, 
            tool,
            response_tx: None,
            workflow_context: Arc::new(RwLock::new(Context::default())),
        }
    }

    /// Set a channel to receive chat responses
    pub fn with_response_channel(mut self, tx: tokio::sync::mpsc::UnboundedSender<ChatResponse>) -> Arc<Self> {
        self.response_tx = Some(tx);
        Arc::new(self)
    }

    fn emit_response(&self, response: ChatResponse) {
        if let Some(tx) = &self.response_tx {
            let _ = tx.send(response);
        }
    }

    pub async fn execute(&self, id: &FlowId, input: &Variables) -> anyhow::Result<Variables> {
        // Check if this is a new conversation
        if input.get("new_conversation").is_some_and(|v| v.as_bool().unwrap_or(false)) {
            *self.workflow_context.write() = Context::default();
        }
        
        match id {
            FlowId::Agent(id) => self.init_agent(id, input).await,
            FlowId::Workflow(id) => self.init_workflow(id, input).await,
        }
    }

    fn init_default_tool_definitions(&self) -> Vec<ToolDefinition> {
        self.tool.list()
    }

    fn init_smart_tool_definitions(&self) -> Vec<ToolDefinition> {
        self.arena
            .tools
            .iter()
            .map(|a| a.to_tool_definition())
            .collect()
    }

    fn init_tool_definitions(&self, tools: &[ToolName]) -> Vec<ToolDefinition> {
        let required_tools = tools.iter().collect::<HashSet<_>>();
        let default_tools = self.init_default_tool_definitions();
        let smart_tools = self.init_smart_tool_definitions();

        default_tools
            .into_iter()
            .chain(smart_tools)
            .filter(|tool| required_tools.contains(&tool.name))
            .collect::<Vec<_>>()
    }

    fn init_agent_context(&self, agent: &Agent, input: &Variables) -> anyhow::Result<Context> {
        let current_context = self.workflow_context.read().clone();
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

        let user_message = agent.user_prompt.render(input)?;
        
        // Keep existing context messages except system message
        let mut new_context = Context::default();
        
        // First add system message
        new_context = new_context.set_first_system_message(system_message);
        
        // Then add all non-system messages from existing context
        if !current_context.messages.is_empty() {
            for msg in current_context.messages.iter() {
                match msg {
                    ContextMessage::ContentMessage(content_msg) if content_msg.role != Role::System => {
                        new_context = new_context.add_message(msg.clone());
                    }
                    ContextMessage::ToolMessage(_) => {
                        new_context = new_context.add_message(msg.clone());
                    }
                    _ => {} // Skip system messages
                }
            }
        }
        
        // Add the new user message
        new_context = new_context.add_message(ContextMessage::user(user_message));
        
        // Add tools
        new_context = new_context.extend_tools(tool_defs);
        
        Ok(new_context)
    }

    async fn collect_tool_calls(
        &self,
        response: impl Stream<Item = anyhow::Result<ChatCompletionMessage>> + Unpin,
        tool_supported: bool,
    ) -> anyhow::Result<(String, Vec<ToolCallFull>, Option<ChatCompletionMessage>)> {
        use futures::StreamExt;
        let mut content_buffer = String::new();
        let mut tool_parts = Vec::new();

        let mut last_message = None;
        let mut messages = response;
        while let Some(message_result) = messages.next().await {
            let message = message_result?;
            last_message = Some(message.clone());
            
            // Handle content
            if let Some(content) = message.content {
                self.emit_response(ChatResponse::Text(content.as_str().to_string()));
                content_buffer.push_str(content.as_str());
            }

            // Handle tool calls
            if tool_supported {
                for tool_call in message.tool_call.iter() {
                    if let ToolCall::Part(part) = tool_call {
                        if part.name.is_some() {
                            if let Some(name) = &part.name {
                                self.emit_response(ChatResponse::ToolCallDetected(name.clone()));
                            }
                        }
                        self.emit_response(ChatResponse::ToolCallArgPart(part.arguments_part.clone()));
                        tool_parts.push(part.clone());
                    }
                }
            }
        }

        let tool_calls = if tool_supported {
            if tool_parts.is_empty() {
                vec![]
            } else {
                let calls = ToolCallFull::try_from_parts(&tool_parts)?;
                for call in &calls {
                    self.emit_response(ChatResponse::ToolCallStart(call.clone()));
                }
                calls
            }
        } else {
            let calls = ToolCallFull::try_from_xml(&content_buffer)?;
            for call in &calls {
                self.emit_response(ChatResponse::ToolCallStart(call.clone()));
            }
            calls
        };
        
        Ok((content_buffer, tool_calls, last_message))
    }

    fn find_tool(&self, name: &ToolName) -> Option<&SmartTool<Variables>> {
        self.arena.tools.iter().find(|tool| tool.name == *name)
    }

    async fn execute_tool(&self, tool_call: &ToolCallFull) -> anyhow::Result<ToolResult> {
        self.emit_response(ChatResponse::ToolCallDetected(tool_call.name.clone()));
        let smart_tool = self.find_tool(&tool_call.name);
        if let Some(tool) = smart_tool {
            let input = Variables::from(tool_call.arguments.clone());
            match self.execute(&tool.run, &input).await {
                Ok(output) => {
                    let output = serde_json::to_string(&output).with_context(|| {
                        format!(
                            "Failed to serialize output of smart tool: {}",
                            tool.name.as_str()
                        )
                    })?;
                    let result = ToolResult::from(tool_call.clone()).success(output);
                    self.emit_response(ChatResponse::ToolCallEnd(result.clone()));
                    Ok(result)
                }
                Err(error) => Ok(ToolResult::from(tool_call.clone()).failure(error.to_string())),
            }
        } else {
            let result = self.tool.call(tool_call.clone()).await;
            self.emit_response(ChatResponse::ToolCallEnd(result.clone()));
            Ok(result)
        }
    }

    fn find_workflow(&self, id: &WorkflowId) -> anyhow::Result<&Workflow> {
        Ok(self
            .arena
            .workflows
            .iter()
            .find(|w| w.id == *id)
            .ok_or(Error::WorkflowUndefined(id.clone()))?)
    }

    fn find_agent(&self, id: &AgentId) -> anyhow::Result<&Agent> {
        Ok(self
            .arena
            .agents
            .iter()
            .find(|a| a.id == *id)
            .ok_or(Error::AgentUndefined(id.clone()))?)
    }

    #[async_recursion]
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
        let agent = self.find_agent(agent)?;
        let mut context = self.init_agent_context(agent, input)?;
        let output = Variables::default();

        loop {
            context = self.execute_transform(&agent.transforms, context).await?;
            self.update_workflow_context(context.clone());
            let mut response = self.provider.chat(&agent.model, context.clone()).await?;
            let tool_supported = self.provider.parameters(&agent.model).await?.tool_supported;

            let (content, tool_calls, message) = self
                .collect_tool_calls(&mut response, tool_supported)
                .await?;
            
            // Get usage from the last message
            if let Some(msg) = message {
                if let Some(usage) = msg.usage {
                    self.emit_response(ChatResponse::Usage(usage));
                }
            }
            
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
                .add_tool_results(tool_results.clone());
            
            self.update_workflow_context(context.clone());
            
            if tool_results.is_empty() {
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
                        .map(|flow_id| self.init_flow(flow_id, &variables, workflow)),
                )
                .await
                .into_iter()
                .collect::<anyhow::Result<Vec<_>>>()
                .map(Variables::from)
            }
            FlowId::Workflow(id) => self.init_workflow(id, input).await,
        }
    }

    fn update_workflow_context(&self, context: Context) {
        *self.workflow_context.write() = context;
    }

    async fn init_workflow(&self, id: &WorkflowId, input: &Variables) -> anyhow::Result<Variables> {
        let workflow = self.find_workflow(id)?;
        join_all(
            workflow
                .head_flow()
                .iter()
                .map(|flow_id| self.init_flow(flow_id, input, workflow)),
        )
        .await
        .into_iter()
        .collect::<anyhow::Result<Vec<_>>>()
        .map(Variables::from)
    }
}
