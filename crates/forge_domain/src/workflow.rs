use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::workflow_config::WorkflowConfig;
use crate::{Agent, AgentId, ModelId};

#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,

    #[merge(strategy = crate::merge::option)]
    pub variables: Option<HashMap<String, Value>>,

    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub commands: Vec<Command>,

    #[merge(strategy = crate::merge::option)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<ModelId>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct Command {
    #[merge(strategy = crate::merge::std::overwrite)]
    pub name: String,

    #[merge(strategy = crate::merge::std::overwrite)]
    pub description: String,

    #[merge(strategy = crate::merge::option)]
    pub value: Option<String>,
}

impl Workflow {
    /// Create a new workflow from a WorkflowConfig
    pub fn from_config(config: &WorkflowConfig) -> Self {
        Self {
            agents: config.agents.clone(),
            variables: config.variables.clone(),
            commands: config.commands.clone(),
            model: config.model.clone(),
        }
    }

    fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;

    #[test]
    fn test_from_config() {
        // Create a sample config
        let mut config = WorkflowConfig::default();
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
        let workflow = Workflow::from_config(&config);

        // Verify
        assert_eq!(workflow.agents.len(), 1);
        assert_eq!(workflow.agents[0].id, AgentId::new("test-agent"));
        assert!(workflow.variables.is_some());
        assert_eq!(workflow.variables.as_ref().unwrap().len(), 2);
        assert_eq!(workflow.commands.len(), 1);
        assert_eq!(workflow.commands[0].name, "test-command");
        assert_eq!(workflow.model, Some(ModelId::new("test-model")));
    }
}
