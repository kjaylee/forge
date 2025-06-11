use derive_setters::Setters;
use forge_api::{AgentId, ConversationId, ModelId, Provider, Usage, Workflow};

use crate::prompt::ForgePrompt;

//TODO: UIState and ForgePrompt seem like the same thing and can be merged
/// State information for the UI
#[derive(Debug, Default, Clone, Setters)]
#[setters(strip_option)]
pub struct UIState {
    pub conversation_id: Option<ConversationId>,
    pub usage: Usage,
    pub operating_agent: Option<AgentId>,
    pub is_first: bool,
    pub model: Option<ModelId>,
    pub provider: Option<Provider>,
}

impl UIState {
    pub fn new(workflow: Workflow) -> Self {
        let operating_agent = workflow
            .variables
            .get("operating_agent")
            .and_then(|value| value.as_str())
            .and_then(|agent_id_str| {
                // Validate that the agent exists in the workflow before creating AgentId
                let agent_id = AgentId::new(agent_id_str);
                if workflow.agents.iter().any(|agent| agent.id == agent_id) {
                    Some(agent_id)
                } else {
                    None
                }
            })
            .or_else(|| workflow.agents.first().map(|agent| agent.id.clone()));

        Self {
            conversation_id: Default::default(),
            usage: Default::default(),
            is_first: true,
            model: workflow.model,
            operating_agent,
            provider: Default::default(),
        }
    }
}

impl From<UIState> for ForgePrompt {
    fn from(state: UIState) -> Self {
        ForgePrompt {
            usage: Some(state.usage),
            model: state.model,
            agent_id: state.operating_agent.unwrap_or(AgentId::new("Forge")),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use forge_api::{Agent, Workflow};
    use pretty_assertions::assert_eq;
    use serde_json::Value;

    use super::*;

    #[test]
    fn test_ui_state_new_with_valid_operating_agent() {
        // Arrange
        let agent = Agent::new("test-agent");
        let mut variables = HashMap::new();
        variables.insert(
            "operating_agent".to_string(),
            Value::String("test-agent".to_string()),
        );

        let fixture = Workflow::new()
            .agents(vec![agent.clone()])
            .variables(variables);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        assert_eq!(actual.operating_agent, Some(AgentId::new("test-agent")));
    }

    #[test]
    fn test_ui_state_new_with_invalid_operating_agent() {
        // Arrange
        let agent = Agent::new("valid-agent");
        let mut variables = HashMap::new();
        variables.insert(
            "operating_agent".to_string(),
            Value::String("invalid-agent".to_string()),
        );

        let fixture = Workflow::new()
            .agents(vec![agent.clone()])
            .variables(variables);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        // Should fall back to the first agent when operating_agent is invalid
        assert_eq!(actual.operating_agent, Some(AgentId::new("valid-agent")));
    }

    #[test]
    fn test_ui_state_new_with_no_operating_agent_variable() {
        // Arrange
        let agent = Agent::new("default-agent");
        let fixture = Workflow::new().agents(vec![agent.clone()]);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        // Should use the first agent when no operating_agent variable is set
        assert_eq!(actual.operating_agent, Some(AgentId::new("default-agent")));
    }

    #[test]
    fn test_ui_state_new_with_no_agents() {
        // Arrange
        let mut variables = HashMap::new();
        variables.insert(
            "operating_agent".to_string(),
            Value::String("nonexistent-agent".to_string()),
        );

        let fixture = Workflow::new().variables(variables);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        // Should be None when no agents exist
        assert_eq!(actual.operating_agent, None);
    }

    #[test]
    fn test_ui_state_new_with_non_string_operating_agent() {
        // Arrange
        let agent = Agent::new("test-agent");
        let mut variables = HashMap::new();
        variables.insert("operating_agent".to_string(), Value::Number(42.into()));

        let fixture = Workflow::new()
            .agents(vec![agent.clone()])
            .variables(variables);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        // Should fall back to the first agent when operating_agent is not a string
        assert_eq!(actual.operating_agent, Some(AgentId::new("test-agent")));
    }

    #[test]
    fn test_ui_state_new_copies_workflow_model() {
        // Arrange
        let agent = Agent::new("test-agent");
        let model = ModelId::new("test-model");
        let fixture = Workflow::new().agents(vec![agent]).model(model.clone());

        // Act
        let actual = UIState::new(fixture);

        // Assert
        assert_eq!(actual.model, Some(model));
    }

    #[test]
    fn test_ui_state_new_sets_default_values() {
        // Arrange
        let fixture = Workflow::new();

        // Act
        let actual = UIState::new(fixture);

        // Assert
        assert_eq!(actual.conversation_id, None);
        assert_eq!(actual.is_first, true);
        assert_eq!(actual.provider, None);
        assert_eq!(actual.operating_agent, None);
    }

    #[test]
    fn test_ui_state_new_multiple_agents_with_valid_operating_agent() {
        // Arrange
        let agent1 = Agent::new("agent1");
        let agent2 = Agent::new("agent2");
        let agent3 = Agent::new("agent3");
        let mut variables = HashMap::new();
        variables.insert(
            "operating_agent".to_string(),
            Value::String("agent2".to_string()),
        );

        let fixture = Workflow::new()
            .agents(vec![agent1, agent2, agent3])
            .variables(variables);

        // Act
        let actual = UIState::new(fixture);

        // Assert
        // Should select the specified agent, not the first one
        assert_eq!(actual.operating_agent, Some(AgentId::new("agent2")));
    }
}
