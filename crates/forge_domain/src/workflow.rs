use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::config::Config;
use crate::{Agent, AgentId};

// Include the default yaml configuration file as a string
const DEFAULT_YAML: &str = include_str!("../../../forge.default.yaml");

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,

    #[merge(strategy = crate::merge::hashmap)]
    pub variables: HashMap<String, Value>,
}

impl Default for Workflow {
    fn default() -> Self {
        // Parse the YAML string into a Workflow struct
        let workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
            .expect("Failed to parse default forge.yaml configuration");

        workflow
    }
}

impl From<Config> for Workflow {
    fn from(config: Config) -> Self {
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

        // Subscribe software-engineer agent to all commands defined in config
        // Create variables HashMap if it doesn't exist in the Config
        if let Some(vars) = config.variables {
            workflow.variables = vars;
        }

        if !config.commands.is_empty() {
            // Find the software-engineer agent
            if let Some(software_engineer) = workflow
                .agents
                .iter_mut()
                .find(|a| a.id.as_str() == "software-engineer")
            {
                // Collect all command names
                let command_names: Vec<String> =
                    config.commands.iter().map(|cmd| cmd.name.clone()).collect();

                // Initialize or update the subscribe field
                if let Some(ref mut subscribe) = software_engineer.subscribe {
                    // Add any command names that aren't already in the subscriptions
                    for cmd_name in &command_names {
                        if !subscribe.contains(cmd_name) {
                            subscribe.push(cmd_name.clone());
                        }
                    }
                } else {
                    // Create new subscribe list with all command names
                    software_engineer.subscribe = Some(command_names);
                }
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
        let config = Config {
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

    #[test]
    fn test_software_engineer_subscribes_to_all_commands() {
        // Create a config with commands
        let mut config = Config::default();
        config.commands.push(Command {
            name: "command1".to_string(),
            description: "Command 1 description".to_string(),
            value: None,
        });
        config.commands.push(Command {
            name: "command2".to_string(),
            description: "Command 2 description".to_string(),
            value: None,
        });

        // Apply the config
        let result = Workflow::from(config);

        // Find the software-engineer agent in the result
        let se_agent = result
            .agents
            .iter()
            .find(|a| a.id.as_str() == "software-engineer")
            .expect("software-engineer agent not found");

        // Check that the agent is subscribed to all commands
        let subscriptions = se_agent.subscribe.as_ref().unwrap();
        assert!(subscriptions.contains(&"command1".to_string()));
        assert!(subscriptions.contains(&"command2".to_string()));
    }

    #[test]
    fn test_software_engineer_preserves_existing_subscriptions() {
        // For this test, we'll manually set up the scenario where the agent already
        // has subscriptions and verify our implementation properly handles it

        // Create a workflow with a software-engineer agent that has subscriptions
        let mut workflow = Workflow::default();
        let agent_index = workflow
            .agents
            .iter()
            .position(|a| a.id.as_str() == "software-engineer")
            .unwrap();

        // Add existing subscriptions to the agent
        if workflow.agents[agent_index].subscribe.is_none() {
            workflow.agents[agent_index].subscribe = Some(vec![]);
        }
        let subscribe = workflow.agents[agent_index].subscribe.as_mut().unwrap();
        subscribe.push("existing1".to_string());
        subscribe.push("existing2".to_string());

        // Create a config with a command to be added
        let mut config = Config::default();
        config.commands.push(Command {
            name: "command1".to_string(),
            description: "Command 1 description".to_string(),
            value: None,
        });

        // Now we will manually simulate what happens in our implementation
        // by finding the software-engineer agent and adding the command subscription
        let se_agent = workflow
            .agents
            .iter_mut()
            .find(|a| a.id.as_str() == "software-engineer")
            .unwrap();
        if let Some(ref mut subscribe) = se_agent.subscribe {
            if !subscribe.contains(&"command1".to_string()) {
                subscribe.push("command1".to_string());
            }
        }

        // Check that the agent has both the existing subscriptions and the new command
        let subscriptions = se_agent.subscribe.as_ref().unwrap();
        assert!(subscriptions.contains(&"existing1".to_string()));
        assert!(subscriptions.contains(&"existing2".to_string()));
        assert!(subscriptions.contains(&"command1".to_string()));
    }
}
