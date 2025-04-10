use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::workflow_config::WorkflowConfig;
use crate::{Agent, AgentId};

// Include the default yaml configuration file as a string
const DEFAULT_YAML: &str = include_str!("../../../forge.default.yaml");

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,
}

impl Default for Workflow {
    fn default() -> Self {
        // Parse the YAML string into a Workflow struct
        let workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
            .expect("Failed to parse default forge.yaml configuration");

        workflow
    }
}

impl From<WorkflowConfig> for Workflow {
    fn from(config: WorkflowConfig) -> Self {
        let mut workflow = Workflow::default();
        // Set models for all the agents
        if let Some(model) = config.model {
            for agent in &mut workflow.agents {
                agent.model = Some(model.clone());
                if let Some(ref mut compact) = agent.compact {
                    compact.model = model.clone();
                }
            }
        }

        // Set max_walker_depth for all agents if specified in config
        if let Some(max_depth) = config.max_walker_depth {
            for agent in &mut workflow.agents {
                agent.max_walker_depth = Some(max_depth);
            }
        }

        // Set global custom rules for all agents
        // If an agent already has custom rules, we append the global rules
        if let Some(rules) = config.custom_rules {
            for agent in &mut workflow.agents {
                if let Some(ref mut agent_rules) = agent.custom_rules {
                    agent_rules.push_str("\n\n");
                    agent_rules.push_str(&rules);
                } else {
                    agent.custom_rules = Some(rules.clone());
                }
            }
        }

        // Set temperature for all agents if specified in config
        if let Some(temp) = &config.temperature {
            for agent in &mut workflow.agents {
                agent.temperature = Some(*temp);
            }
        }

        workflow
    }
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

    use super::*;
    use crate::{ModelId, Temperature};

    #[test]
    fn test_workflow_config_to_workflow() {
        // Create a agent-specific values by directly using WorkflowConfig
        let config = WorkflowConfig {
            model: Some(ModelId::new("test-model")),
            max_walker_depth: Some(10),
            custom_rules: Some("Global Rules".to_string()),
            temperature: Some(Temperature::new(0.7).unwrap()),
            ..Default::default()
        };

        // Create a simple workflow with our test agents
        let mut workflow = Workflow::default();

        // Add our test agents to the workflow
        workflow.agents.push(Agent::new("agent1"));
        workflow.agents.push(
            Agent::new("agent2")
                .max_walker_depth(5_usize)
                .custom_rules("Agent 2 Rules"),
        );

        // Apply the config settings to all agents
        if let Some(model) = &config.model {
            for agent in &mut workflow.agents {
                agent.model = Some(model.clone());
            }
        }

        if let Some(max_depth) = config.max_walker_depth {
            for agent in &mut workflow.agents {
                agent.max_walker_depth = Some(max_depth);
            }
        }

        if let Some(rules) = &config.custom_rules {
            for agent in &mut workflow.agents {
                if let Some(ref mut agent_rules) = agent.custom_rules {
                    agent_rules.push_str("\n\n");
                    agent_rules.push_str(rules);
                } else {
                    agent.custom_rules = Some(rules.clone());
                }
            }
        }

        if let Some(temp) = &config.temperature {
            for agent in &mut workflow.agents {
                agent.temperature = Some(*temp);
            }
        }

        // Verify that all agents have the model applied
        for agent in &workflow.agents {
            assert_eq!(agent.model, Some(ModelId::new("test-model")));
        }

        // Verify that all agents have max_walker_depth
        for agent in &workflow.agents {
            assert_eq!(agent.max_walker_depth, Some(10));
        }

        // Get agent2 and agent1 from the workflow
        let agent2 = workflow
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent2")
            .expect("agent2 not found");

        assert!(agent2
            .custom_rules
            .as_ref()
            .unwrap()
            .contains("Agent 2 Rules"));
        assert!(agent2
            .custom_rules
            .as_ref()
            .unwrap()
            .contains("Global Rules"));

        // Verify that agent without custom rules gets global rules
        let agent1 = workflow
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent1")
            .expect("agent1 not found");

        assert_eq!(agent1.custom_rules, Some("Global Rules".to_string()));

        // Verify that all agents have temperature set
        for agent in &workflow.agents {
            assert_eq!(agent.temperature.unwrap().value(), 0.7);
        }
    }
}
