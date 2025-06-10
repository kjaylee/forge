use std::sync::Arc;

use async_trait::async_trait;
use forge_domain::{
    Agent, ChatResponse, ExecutableTool, JsonTool, NamedTool, Tool, ToolCallContext, ToolDefinition, ToolDescription, ToolName, ToolOutput
};
use forge_tool_macros::ToolDescription;
use schemars::{schema::RootSchema, JsonSchema};
use serde::{Deserialize, Serialize};

use crate::Infrastructure;

/// Input schema for calling another agent
#[derive(Default, Debug, Clone, Serialize, Deserialize, JsonSchema, ToolDescription)]
pub struct AgentInput {
    /// The task or message to send to the agent
    pub task: String,
}

/// Tool for calling other agents
pub struct AgentTool<F> {
    id: String,
    description: Option<String>,
    #[allow(dead_code)]
    infra: Arc<F>,
}

impl<F: Infrastructure> AgentTool<F> {
    pub fn new(infra: Arc<F>, agent_id: String, agent_description: Option<String>) -> Self {
        Self { infra, id: agent_id, description: agent_description }
    }

    pub fn to_tool(self) -> Tool {
        let input: RootSchema = schemars::schema_for!(AgentInput);
        let def = ToolDefinition {
            name: ToolName::new(self.id.clone()),
            description: self.description.clone().unwrap_or_default(),
            input_schema: input,
        };
        let exec = Box::new(JsonTool::new(self));
        let tool = Tool { definition: def, executable: exec };
        tool
    }

    /// Create an AgentTool instance for a specific agent
    pub fn for_agent<I: Infrastructure>(infra: Arc<I>, agent: &Agent) -> AgentTool<I> {
        AgentTool::new(
            infra,
            agent.id.as_str().to_string(),
            agent.description.clone(),
        )
    }
}

#[async_trait]
impl<F: Infrastructure> ExecutableTool for AgentTool<F> {
    type Input = AgentInput;

    async fn call(
        &self,
        context: &mut ToolCallContext,
        input: Self::Input,
    ) -> anyhow::Result<ToolOutput> {
        // Send a message back to the stream indicating we're calling another agent
        if let Some(sender) = context.sender.as_ref() {
            let message = format!(
                "🔄 Calling agent '{}' with task: {}",
                self.id, input.task
            );

            let _ = sender
                .send(Ok(ChatResponse::Text {
                    text: message,
                    is_complete: false,
                    is_md: false,
                    is_summary: false,
                }))
                .await;
        }

        Ok(ToolOutput::text("Tool called successfully".into()))
    }
}

impl<F: Infrastructure> NamedTool for AgentTool<F> {
    fn tool_name() -> ToolName {
        ToolName::new("agent_tool")
    }
}

impl<F: Infrastructure> ToolDescription for AgentTool<F> {
    fn description(&self) -> String {
        format!(
            "Call the {} agent when {}",
            self.id,
            self.description
                .as_deref()
                .unwrap_or("No description available.")
        )
    }
}

// #[cfg(test)]
// mod tests {
//     use forge_domain::ToolName;
//     use pretty_assertions::assert_eq;

//     use super::*;
//     use crate::tools::registry::tests::Stub;

//     #[tokio::test]
//     async fn test_agent_tool_call() {
//         let fixture = AgentTool::new(
//             Arc::new(Stub::default()),
//             "test-agent".to_string(),
//             Some("A test agent".to_string()),
//         );
//         let input = serde_json::json!({
//             "task": "Test task for the agent",
//             "event_name": null
//         });

//         let mut context = ToolCallContext::default();
//         let actual = fixture.call(&mut context, input).await;

//         assert!(actual.is_ok());
//         let output = actual.unwrap();
//         let expected_text = "Agent 'test-agent' called with task: 'Test task
// for the agent'. This will trigger the test_agent/user_task_init event.";
//         assert!(output.as_str().unwrap().contains(expected_text));
//     }

//     #[test]
//     fn test_tool_definition_for_agent() {
//         let mut agent = Agent::new("software-designer");
//         agent = agent.description("A specialized agent for software design
// and planning");

//         let actual =
// AgentTool::<Stub>::tool_definition_for_agent(&agent).unwrap();

//         let expected_name = ToolName::new("software-designer");
//         let expected_description = "Call the software-designer agent. A
// specialized agent for software design and planning";

//         assert_eq!(actual.name, expected_name);
//         assert_eq!(actual.description, expected_description);
//     }

//     #[test]
//     fn test_tool_definition_for_agent_no_description() {
//         let agent = Agent::new("test-agent");

//         let actual =
// AgentTool::<Stub>::tool_definition_for_agent(&agent).unwrap();

//         let expected_name = ToolName::new("test-agent");
//         let expected_description = "Call the test-agent agent. No description
// available.";

//         assert_eq!(actual.name, expected_name);
//         assert_eq!(actual.description, expected_description);
//     }

//     #[test]
//     fn test_for_agent_creation() {
//         let mut agent = Agent::new("test-agent");
//         agent = agent.description("Test agent description");

//         let tool = AgentTool::<Stub>::for_agent(Arc::new(Stub::default()),
// &agent);

//         assert_eq!(tool.agent_id, "test-agent");
//         assert_eq!(
//             tool.agent_description,
//             Some("Test agent description".to_string())
//         );
//     }
// }
