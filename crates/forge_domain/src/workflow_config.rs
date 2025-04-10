use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Agent, AgentId, Command, ModelId, Workflow};

/// Configuration for a workflow that contains all settings
/// required to initialize a workflow.
#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct WorkflowConfig {
    /// The agents that are part of this workflow
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,

    /// Variables that can be used in templates
    #[merge(strategy = crate::merge::option)]
    pub variables: Option<HashMap<String, Value>>,

    /// Commands that can be used to interact with the workflow
    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub commands: Vec<Command>,

    /// Default model ID to use for agents in this workflow
    #[merge(strategy = crate::merge::option)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<ModelId>,
}

impl WorkflowConfig {
    /// Creates a new `WorkflowConfig` with default values
    pub fn new() -> Self {
        Self::default()
    }

    /// Converts this configuration into a `Workflow`
    pub fn to_workflow(&self) -> Workflow {
        Workflow {
            agents: self.agents.clone(),
            variables: self.variables.clone(),
            commands: self.commands.clone(),
            model: self.model.clone(),
        }
    }

    /// Finds an agent by its ID
    pub fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    /// Gets an agent by its ID, returning an error if not found
    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }
}

// Conversions from Workflow to WorkflowConfig have been removed
// to enforce one-way conversion from WorkflowConfig to Workflow only

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;
    use crate::{Agent, AgentId, ModelId};

    #[test]
    fn test_new_workflow_config() {
        let config = WorkflowConfig::new();
        assert!(config.agents.is_empty());
        assert_eq!(config.variables, None);
        assert!(config.commands.is_empty());
        assert_eq!(config.model, None);
    }

    #[test]
    fn test_conversion_from_config_to_workflow() {
        // Create a sample config
        let mut config = WorkflowConfig::new();
        config.agents = vec![Agent::new("test-agent")];
        config.variables = Some(HashMap::from([
            ("key1".to_string(), json!("value1")),
            ("key2".to_string(), json!(123)),
        ]));
        config.commands = vec![Command {
            name: "test-command".to_string(),
            description: "A test command".to_string(),
            value: Some("test-value".to_string()),
        }];
        config.model = Some(ModelId::new("test-model"));

        // Convert to workflow
        let workflow = config.to_workflow();

        // Verify
        assert_eq!(workflow.agents.len(), 1);
        assert_eq!(workflow.agents[0].id, AgentId::new("test-agent"));
        assert!(workflow.variables.is_some());
        assert_eq!(workflow.variables.as_ref().unwrap().len(), 2);
        assert_eq!(workflow.commands.len(), 1);
        assert_eq!(workflow.commands[0].name, "test-command");
        assert_eq!(workflow.model, Some(ModelId::new("test-model")));
    }

    #[test]
    fn test_find_agent() {
        let mut config = WorkflowConfig::new();
        let agent1 = Agent::new("agent1");
        let agent2 = Agent::new("agent2");
        config.agents = vec![agent1, agent2];

        let found = config.find_agent(&AgentId::new("agent1"));
        assert!(found.is_some());
        assert_eq!(found.unwrap().id, AgentId::new("agent1"));

        let not_found = config.find_agent(&AgentId::new("nonexistent"));
        assert!(not_found.is_none());
    }

    #[test]
    fn test_get_agent() {
        let mut config = WorkflowConfig::new();
        let agent1 = Agent::new("agent1");
        config.agents = vec![agent1];

        let result = config.get_agent(&AgentId::new("agent1"));
        assert!(result.is_ok());
        assert_eq!(result.unwrap().id, AgentId::new("agent1"));

        let error = config.get_agent(&AgentId::new("nonexistent"));
        assert!(error.is_err());
        assert!(matches!(
            error.unwrap_err(),
            crate::Error::AgentUndefined(_)
        ));
    }

    #[test]
    fn test_merge_behavior() {
        // Create base config
        let mut base = WorkflowConfig::new();
        base.agents = vec![Agent::new("agent1")];
        base.model = Some(ModelId::new("base-model"));
        base.commands = vec![Command {
            name: "cmd1".to_string(),
            description: "Command 1".to_string(),
            value: None,
        }];

        // Create other config
        let mut other = WorkflowConfig::new();
        other.agents = vec![Agent::new("agent2")];
        other.model = Some(ModelId::new("other-model"));
        other.commands = vec![Command {
            name: "cmd2".to_string(),
            description: "Command 2".to_string(),
            value: None,
        }];

        // Merge configs
        base.merge(other);

        // Verify merged result maintains expected behavior
        assert_eq!(base.agents.len(), 2);
        assert!(base.agents.iter().any(|a| a.id == AgentId::new("agent1")));
        assert!(base.agents.iter().any(|a| a.id == AgentId::new("agent2")));
        assert_eq!(base.model, Some(ModelId::new("other-model")));
        assert_eq!(base.commands.len(), 2);
        assert!(base.commands.iter().any(|c| c.name == "cmd1"));
        assert!(base.commands.iter().any(|c| c.name == "cmd2"));
    }
}
