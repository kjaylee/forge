use std::collections::{HashMap, VecDeque};

use derive_more::derive::Display;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::{
    Agent, AgentId, Context, Error, Event, Mode, ModeConfig, ModelId, Result, ToolName, Workflow,
};

#[derive(Debug, Display, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
#[serde(transparent)]
pub struct ConversationId(Uuid);

impl ConversationId {
    pub fn generate() -> Self {
        Self(Uuid::new_v4())
    }

    pub fn into_string(&self) -> String {
        self.0.to_string()
    }

    pub fn parse(value: impl ToString) -> Result<Self> {
        Ok(Self(
            Uuid::parse_str(&value.to_string()).map_err(Error::ConversationId)?,
        ))
    }
}

#[derive(Debug, Setters, Serialize, Deserialize, Clone)]
pub struct Conversation {
    pub id: ConversationId,
    pub archived: bool,
    pub state: HashMap<AgentId, AgentState>,
    pub agents: Vec<Agent>,
    pub events: Vec<Event>,
    pub mode: Mode,
    pub workflow: Workflow,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AgentState {
    pub turn_count: u64,
    pub context: Option<Context>,
    /// holds the events that are waiting to be processed
    pub queue: VecDeque<Event>,
}

impl Conversation {
    pub const MAIN_AGENT_NAME: &str = "software-engineer";

    /// Returns the model of the main agent
    ///
    /// # Errors
    /// - `AgentUndefined` if the main agent doesn't exist
    /// - `NoModelDefined` if the main agent doesn't have a model defined
    pub fn main_model(&self) -> Result<ModelId> {
        let agent = self.get_agent(&AgentId::new(Self::MAIN_AGENT_NAME))?;
        agent
            .model
            .clone()
            .ok_or(Error::NoModelDefined(agent.id.clone()))
    }
    /// Sets the model of the main agent
    ///
    /// # Errors
    /// - `AgentUndefined` if the main agent doesn't exist
    pub fn set_main_model(&mut self, model: ModelId) -> Result<()> {
        // Find the main agent and update its model
        let agent_pos = self
            .agents
            .iter()
            .position(|a| a.id.as_str() == Self::MAIN_AGENT_NAME)
            .ok_or_else(|| Error::AgentUndefined(AgentId::new(Self::MAIN_AGENT_NAME)))?;

        // Update the model
        self.agents[agent_pos].model = Some(model);

        Ok(())
    }

    pub fn new(id: ConversationId, workflow: Workflow) -> Self {
        let mut agents = Vec::new();

        for mut agent in workflow.clone().agents.into_iter() {
            if let Some(custom_rules) = workflow.custom_rules.clone() {
                agent.custom_rules = Some(custom_rules);
            }

            if let Some(max_walker_depth) = workflow.max_walker_depth {
                agent.max_walker_depth = Some(max_walker_depth);
            }

            if let Some(temperature) = workflow.temperature {
                agent.temperature = Some(temperature);
            }

            if let Some(model) = workflow.model.clone() {
                agent.model = Some(model);
            }

            if let Some(tool_supported) = workflow.tool_supported {
                agent.tool_supported = Some(tool_supported);
            }

            if agent.id.as_str() == Conversation::MAIN_AGENT_NAME {
                // Add command subscriptions to the main agent
                let commands = workflow
                    .commands
                    .iter()
                    .map(|c| c.name.clone())
                    .collect::<Vec<_>>();
                if let Some(ref mut subscriptions) = agent.subscribe {
                    subscriptions.extend(commands);
                } else {
                    agent.subscribe = Some(commands);
                }

                // Add mode-specific tools and system prompts from the workflow to the agent
                // Apply configuration for each mode
                for (mode, mode_config) in workflow.modes.iter() {
                    // Add mode configuration to the agent's modes
                    let agent_mode_config = agent
                        .modes
                        .entry(mode.clone())
                        .or_insert_with(ModeConfig::new);

                    // Add mode-specific tools
                    if let Some(mode_tools) = &mode_config.tools {
                        // Add tools to the agent's mode configuration
                        if let Some(ref mut agent_tools) = agent_mode_config.tools {
                            agent_tools.extend(mode_tools.clone());
                        } else {
                            agent_mode_config.tools = Some(mode_tools.clone());
                        }

                        // Legacy mode-specific tools (act_tools and
                        // plan_tools) have been removed
                    }

                    // Add mode-specific system prompt to the agent's mode configuration
                    if mode_config.system_prompt.is_some() {
                        agent_mode_config.system_prompt = mode_config.system_prompt.clone();
                    }
                }
            }

            agents.push(agent);
        }

        // Use the default mode (Act)
        let mode = Mode::default();

        Self {
            id,
            archived: false,
            state: Default::default(),
            agents,
            events: Default::default(),
            mode,
            workflow,
        }
    }

    pub fn turn_count(&self, id: &AgentId) -> Option<u64> {
        self.state.get(id).map(|s| s.turn_count)
    }

    /// Returns all the agents that are subscribed to the given event.
    pub fn subscriptions(&self, event_name: &str) -> Vec<Agent> {
        self.agents
            .iter()
            .filter(|a| {
                // Filter out disabled agents
                !a.disable.unwrap_or_default()
            })
            .filter(|a| {
                self.turn_count(&a.id).unwrap_or_default() < a.max_turns.unwrap_or(u64::MAX)
            })
            .filter(|a| {
                a.subscribe
                    .as_ref()
                    .is_some_and(|subs| subs.contains(&event_name.to_string()))
            })
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Returns the agent with the given id or an error if it doesn't exist
    pub fn get_agent(&self, id: &AgentId) -> Result<&Agent> {
        self.agents
            .iter()
            .find(|a| a.id == *id)
            .ok_or(Error::AgentUndefined(id.clone()))
    }

    pub fn context(&self, id: &AgentId) -> Option<&Context> {
        self.state.get(id).and_then(|s| s.context.as_ref())
    }

    pub fn rfind_event(&self, event_name: &str) -> Option<&Event> {
        self.state
            .values()
            .flat_map(|state| state.queue.iter().rev())
            .find(|event| event.name == event_name)
    }

    /// Returns the allowed tools for a specific agent based on the current mode
    pub fn get_allowed_tools(&self, agent_id: &AgentId) -> Result<Vec<ToolName>> {
        let agent = self.get_agent(agent_id)?;
        let current_mode = &self.mode;

        let mut allowed_tools = Vec::new();

        // Add general tools (available in all modes)
        if let Some(general_tools) = &agent.tools {
            allowed_tools.extend(general_tools.clone());
        }

        // Add mode-specific tools from the agent's modes
        if let Some(mode_config) = agent.modes.get(current_mode) {
            if let Some(mode_tools) = &mode_config.tools {
                allowed_tools.extend(mode_tools.clone());
            }
        }

        // Legacy mode-specific tools (act_tools and plan_tools) have been removed

        // Remove duplicates
        allowed_tools.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        allowed_tools.dedup();

        Ok(allowed_tools)
    }

    /// Generates an HTML representation of the conversation
    ///
    /// This method uses Handlebars to render the conversation as HTML
    /// from the template file, including all agents, events, and variables.
    ///
    /// # Errors
    /// - If the template file cannot be found or read
    /// - If the Handlebars template registration fails
    /// - If the template rendering fails
    pub fn to_html(&self) -> String {
        // Instead of using Handlebars, we now use our Element DSL
        crate::conversation_html::render_conversation_html(self)
    }

    /// Add an event to the queue of subscribed agents
    pub fn insert_event(&mut self, event: Event) -> &mut Self {
        let subscribed_agents = self.subscriptions(&event.name);
        self.events.push(event.clone());

        subscribed_agents.iter().for_each(|agent| {
            self.state
                .entry(agent.id.clone())
                .or_default()
                .queue
                .push_back(event.clone());
        });

        self
    }

    /// Gets the next event for a specific agent, if one is available
    ///
    /// If an event is available in the agent's queue, it is popped and
    /// returned. Additionally, if the agent's queue becomes empty, it is
    /// marked as inactive.
    ///
    /// Returns None if no events are available for this agent.
    pub fn poll_event(&mut self, agent_id: &AgentId) -> Option<Event> {
        // if event is present in queue, pop it and return.
        if let Some(agent) = self.state.get_mut(agent_id) {
            if let Some(event) = agent.queue.pop_front() {
                return Some(event);
            }
        }
        None
    }

    /// Dispatches an event to all subscribed agents and activates any inactive
    /// agents
    ///
    /// This method performs two main operations:
    /// 1. Adds the event to the queue of all agents that subscribe to this
    ///    event type
    /// 2. Activates any inactive agents (where is_active=false) that are
    ///    subscribed to the event
    ///
    /// Returns a vector of AgentIds for all agents that were inactive and are
    /// now activated
    pub fn dispatch_event(&mut self, event: Event) -> Vec<AgentId> {
        let name = event.name.as_str();
        let mut agents = self.subscriptions(name);

        let inactive_agents = agents
            .iter_mut()
            .filter_map(|agent| {
                let is_inactive = self
                    .state
                    .get(&agent.id)
                    .map(|state| state.queue.is_empty())
                    .unwrap_or(true);
                if is_inactive {
                    Some(agent.id.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        self.insert_event(event);

        inactive_agents
    }
}

#[cfg(test)]
mod tests {
    use crate::{Agent, Command, Error, Mode, ModelId, Temperature, Workflow};

    #[test]
    fn test_conversation_new_with_empty_workflow() {
        // Arrange
        let id = super::ConversationId::generate();
        let workflow = Workflow::new();

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.id, id);
        assert!(!conversation.archived);
        assert!(conversation.state.is_empty());
        assert!(conversation.agents.is_empty());
        assert!(conversation.events.is_empty());
    }

    #[test]
    fn test_conversation_new_with_workflow_variables() {
        // Arrange
        let id = super::ConversationId::generate();
        let workflow = Workflow::new();

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.id, id);
        // Verify that the default mode is used
        assert_eq!(conversation.mode, Mode::default());
    }

    #[test]
    fn test_conversation_new_applies_workflow_settings_to_agents() {
        // Arrange
        let id = super::ConversationId::generate();
        let agent1 = Agent::new("agent1");
        let agent2 = Agent::new("agent2");

        let workflow = Workflow::new()
            .agents(vec![agent1, agent2])
            .model(ModelId::new("test-model"))
            .max_walker_depth(5)
            .custom_rules("Be helpful".to_string())
            .temperature(Temperature::new(0.7).unwrap())
            .tool_supported(true);

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.agents.len(), 2);

        // Check that workflow settings were applied to all agents
        for agent in &conversation.agents {
            assert_eq!(agent.model, Some(ModelId::new("test-model")));
            assert_eq!(agent.max_walker_depth, Some(5));
            assert_eq!(agent.custom_rules, Some("Be helpful".to_string()));
            assert_eq!(agent.temperature, Some(Temperature::new(0.7).unwrap()));
            assert_eq!(agent.tool_supported, Some(true));
        }
    }

    #[test]
    fn test_conversation_new_preserves_agent_specific_settings() {
        // Arrange
        let id = super::ConversationId::generate();

        // Agent with specific settings
        let agent1 = Agent::new("agent1")
            .model(ModelId::new("agent1-model"))
            .max_walker_depth(10_usize)
            .custom_rules("Agent1 specific rules".to_string())
            .temperature(Temperature::new(0.3).unwrap())
            .tool_supported(false);

        // Agent without specific settings
        let agent2 = Agent::new("agent2");

        let workflow = Workflow::new()
            .agents(vec![agent1, agent2])
            .model(ModelId::new("default-model"))
            .max_walker_depth(5)
            .custom_rules("Default rules".to_string())
            .temperature(Temperature::new(0.7).unwrap())
            .tool_supported(true);

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.agents.len(), 2);

        // Check that agent1's settings were overridden by workflow settings
        let agent1 = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent1")
            .unwrap();
        assert_eq!(agent1.model, Some(ModelId::new("default-model")));
        assert_eq!(agent1.max_walker_depth, Some(5));
        assert_eq!(agent1.custom_rules, Some("Default rules".to_string()));
        assert_eq!(agent1.temperature, Some(Temperature::new(0.7).unwrap()));
        assert_eq!(agent1.tool_supported, Some(true)); // Workflow setting overrides agent setting

        // Check that agent2 got the workflow defaults
        let agent2 = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent2")
            .unwrap();
        assert_eq!(agent2.model, Some(ModelId::new("default-model")));
        assert_eq!(agent2.max_walker_depth, Some(5));
        assert_eq!(agent2.custom_rules, Some("Default rules".to_string()));
        assert_eq!(agent2.temperature, Some(Temperature::new(0.7).unwrap()));
        assert_eq!(agent2.tool_supported, Some(true)); // Workflow setting is
                                                       // applied
    }

    #[test]
    fn test_conversation_new_adds_commands_to_main_agent_subscriptions() {
        // Arrange
        let id = super::ConversationId::generate();

        // Create the main software-engineer agent
        let main_agent = Agent::new(super::Conversation::MAIN_AGENT_NAME);
        // Create a regular agent
        let other_agent = Agent::new("other-agent");

        // Create some commands
        let commands = vec![
            Command {
                name: "cmd1".to_string(),
                description: "Command 1".to_string(),
                prompt: None,
            },
            Command {
                name: "cmd2".to_string(),
                description: "Command 2".to_string(),
                prompt: None,
            },
        ];

        let workflow = Workflow::new()
            .agents(vec![main_agent, other_agent])
            .commands(commands.clone());

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.agents.len(), 2);

        // Check that main agent received command subscriptions
        let main_agent = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == super::Conversation::MAIN_AGENT_NAME)
            .unwrap();

        assert!(main_agent.subscribe.is_some());
        let subscriptions = main_agent.subscribe.as_ref().unwrap();
        assert!(subscriptions.contains(&"cmd1".to_string()));
        assert!(subscriptions.contains(&"cmd2".to_string()));

        // Check that other agent didn't receive command subscriptions
        let other_agent = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == "other-agent")
            .unwrap();

        if other_agent.subscribe.is_some() {
            assert!(!other_agent
                .subscribe
                .as_ref()
                .unwrap()
                .contains(&"cmd1".to_string()));
            assert!(!other_agent
                .subscribe
                .as_ref()
                .unwrap()
                .contains(&"cmd2".to_string()));
        }
    }

    #[test]
    fn test_conversation_new_merges_commands_with_existing_subscriptions() {
        // Arrange
        let id = super::ConversationId::generate();

        // Create the main software-engineer agent with existing subscriptions
        let mut main_agent = Agent::new(super::Conversation::MAIN_AGENT_NAME);
        main_agent.subscribe = Some(vec!["existing-event".to_string()]);

        // Create some commands
        let commands = vec![
            Command {
                name: "cmd1".to_string(),
                description: "Command 1".to_string(),
                prompt: None,
            },
            Command {
                name: "cmd2".to_string(),
                description: "Command 2".to_string(),
                prompt: None,
            },
        ];

        let workflow = Workflow::new()
            .agents(vec![main_agent])
            .commands(commands.clone());

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        let main_agent = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == super::Conversation::MAIN_AGENT_NAME)
            .unwrap();

        assert!(main_agent.subscribe.is_some());
        let subscriptions = main_agent.subscribe.as_ref().unwrap();

        // Should contain both the existing subscription and the new commands
        assert!(subscriptions.contains(&"existing-event".to_string()));
        assert!(subscriptions.contains(&"cmd1".to_string()));
        assert!(subscriptions.contains(&"cmd2".to_string()));
        assert_eq!(subscriptions.len(), 3);
    }

    #[test]
    fn test_main_model_success() {
        // Arrange
        let id = super::ConversationId::generate();
        let main_agent =
            Agent::new(super::Conversation::MAIN_AGENT_NAME).model(ModelId::new("test-model"));

        let workflow = Workflow::new().agents(vec![main_agent]);

        let conversation = super::Conversation::new(id, workflow);

        // Act
        let model_id = conversation.main_model().unwrap();

        // Assert
        assert_eq!(model_id, ModelId::new("test-model"));
    }

    #[test]
    fn test_main_model_agent_not_found() {
        // Arrange
        let id = super::ConversationId::generate();
        let agent = Agent::new("some-other-agent");

        let workflow = Workflow::new().agents(vec![agent]);

        let conversation = super::Conversation::new(id, workflow);

        // Act
        let result = conversation.main_model();

        // Assert
        assert!(matches!(result, Err(Error::AgentUndefined(_))));
    }

    #[test]
    fn test_main_model_no_model_defined() {
        // Arrange
        let id = super::ConversationId::generate();
        let main_agent = Agent::new(super::Conversation::MAIN_AGENT_NAME);
        // No model defined for the agent

        let workflow = Workflow::new().agents(vec![main_agent]);

        let conversation = super::Conversation::new(id, workflow);

        // Act
        let result = conversation.main_model();

        // Assert
        assert!(matches!(result, Err(Error::NoModelDefined(_))));
    }
    #[test]
    fn test_set_main_model_success() {
        // Arrange
        let id = super::ConversationId::generate();
        let main_agent = Agent::new(super::Conversation::MAIN_AGENT_NAME);
        // Initially no model defined

        let workflow = Workflow::new().agents(vec![main_agent]);

        let mut conversation = super::Conversation::new(id, workflow);

        // Act
        let result = conversation.set_main_model(ModelId::new("new-model"));

        // Assert
        assert!(result.is_ok());
        let model = conversation.main_model().unwrap();
        assert_eq!(model, ModelId::new("new-model"));
    }

    #[test]
    fn test_set_main_model_agent_not_found() {
        // Arrange
        let id = super::ConversationId::generate();
        let agent = Agent::new("some-other-agent");

        let workflow = Workflow::new().agents(vec![agent]);

        let mut conversation = super::Conversation::new(id, workflow);

        // Act
        let result = conversation.set_main_model(ModelId::new("new-model"));

        // Assert
        assert!(matches!(result, Err(Error::AgentUndefined(_))));
    }

    #[test]
    fn test_conversation_new_applies_tool_supported_to_agents() {
        // Arrange
        let id = super::ConversationId::generate();
        let agent1 = Agent::new("agent1");
        let agent2 = Agent::new("agent2");

        let workflow = Workflow::new()
            .agents(vec![agent1, agent2])
            .tool_supported(true);

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.agents.len(), 2);

        // Check that workflow tool_supported setting was applied to all agents
        for agent in &conversation.agents {
            assert_eq!(agent.tool_supported, Some(true));
        }
    }

    #[test]
    fn test_conversation_new_respects_agent_specific_tool_supported() {
        // Arrange
        let id = super::ConversationId::generate();

        // Agent with specific setting
        let agent1 = Agent::new("agent1").tool_supported(false);

        // Agent without specific setting
        let agent2 = Agent::new("agent2");

        let workflow = Workflow::new()
            .agents(vec![agent1, agent2])
            .tool_supported(true);

        // Act
        let conversation = super::Conversation::new(id.clone(), workflow);

        // Assert
        assert_eq!(conversation.agents.len(), 2);

        // Check that workflow settings were applied correctly
        // For agent1, the workflow setting should override the agent-specific setting
        let agent1 = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent1")
            .unwrap();
        assert_eq!(agent1.tool_supported, Some(true));

        // For agent2, the workflow setting should be applied
        let agent2 = conversation
            .agents
            .iter()
            .find(|a| a.id.as_str() == "agent2")
            .unwrap();
        assert_eq!(agent2.tool_supported, Some(true));
    }
}
