use async_trait::async_trait;
use forge_display::TitleFormat;
use forge_domain::{
    Agent, ChatResponse, ExecutableTool, NamedTool, ToolCallContext, ToolDescription, ToolName,
    ToolOutput,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Input schema for calling another agent
#[derive(Default, Debug, Clone, Serialize, Deserialize, JsonSchema, ToolDescription)]
pub struct AgentInput {
    /// The task or message to send to the agent
    pub task: String,
}

/// Tool for calling other agents
pub struct AgentTool {
    id: String,
    description: Option<String>,
}

impl AgentTool {
    fn new(agent_id: String, agent_description: Option<String>) -> Self {
        Self { id: agent_id, description: agent_description }
    }
}

#[async_trait]
impl ExecutableTool for AgentTool {
    type Input = AgentInput;

    async fn call(
        &self,
        context: &mut ToolCallContext,
        input: Self::Input,
    ) -> anyhow::Result<ToolOutput> {
        // Send a message back to the stream indicating we're calling another agent
        let title_format =
            TitleFormat::debug(format!("Agent [{}]", self.id)).sub_title(&input.task);
        context.send_text(title_format).await?;

        Ok(ToolOutput::text("Tool called successfully".into()))
    }
}

impl NamedTool for AgentTool {
    fn tool_name(&self) -> ToolName {
        ToolName::new(self.id.as_str())
    }
}

impl ToolDescription for AgentTool {
    fn description(&self) -> String {
        self.description.clone().unwrap_or_default()
    }
}

impl From<&Agent> for AgentTool {
    fn from(agent: &Agent) -> Self {
        AgentTool::new(agent.id.as_str().to_string(), agent.description.clone())
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
