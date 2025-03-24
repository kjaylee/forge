use derive_more::derive::Display;
use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::merge::Key;
use crate::template::Template;
use crate::{Error, EventContext, ModelId, Result, SystemContext, ToolDefinition, ToolName};

// Unique identifier for an agent
#[derive(Debug, Display, Eq, PartialEq, Hash, Clone, Serialize, Deserialize)]
#[serde(transparent)]
pub struct AgentId(String);
impl AgentId {
    // Creates a new agent ID from a string-like value
    pub fn new(id: impl ToString) -> Self {
        Self(id.to_string())
    }

    // Returns the agent ID as a string reference
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<ToolName> for AgentId {
    // Converts a ToolName into an AgentId
    fn from(value: ToolName) -> Self {
        Self(value.into_string())
    }
}

/// Configuration for automatic context compaction
#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct Compaction {
    /// Maximum number of tokens to keep after compaction
    #[merge(strategy = crate::merge::std::overwrite)]
    pub max_tokens: usize,

    /// Maximum number of tokens before triggering compaction
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub token_threshold: Option<usize>,

    /// Maximum number of conversation turns before triggering compaction
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub turn_threshold: Option<usize>,

    /// Maximum number of messages before triggering compaction
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub message_threshold: Option<usize>,

    /// Optional custom prompt template to use during compaction
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub prompt: Option<String>,
    
    /// Optional model ID to use for compaction, overrides the agent's model
    /// Useful when compacting with a cheaper/faster model
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub model: Option<ModelId>,
}

impl Compaction {
    /// Creates a new compaction configuration with the specified maximum token limit
    pub fn new(max_tokens: usize) -> Self {
        Self {
            max_tokens,
            token_threshold: None,
            turn_threshold: None,
            message_threshold: None,
            prompt: None,
            model: None,
        }
    }

    /// Determines if compaction should be triggered based on the current context
    pub fn should_compact(
        &self,
        token_count: usize,
        turn_count: usize,
        message_count: usize,
    ) -> bool {
        // Check if any of the thresholds have been exceeded
        if let Some(token_threshold) = self.token_threshold {
            if token_count >= token_threshold {
                return true;
            }
        }

        if let Some(turn_threshold) = self.turn_threshold {
            if turn_count >= turn_threshold {
                return true;
            }
        }

        if let Some(message_threshold) = self.message_threshold {
            if message_count >= message_threshold {
                return true;
            }
        }

        false
    }
}
#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct Agent {
    /// Controls whether this agent's output should be hidden from the console
    /// When false (default), output is not displayed
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub hide_content: Option<bool>,

    /// Flag to disable this agent, when true agent will not be activated
    /// Default is false (agent is enabled)
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub disable: Option<bool>,

    /// Flag to enable/disable tool support for this agent.
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub tool_supported: Option<bool>,

    // Unique identifier for the agent
    #[merge(strategy = crate::merge::std::overwrite)]
    pub id: AgentId,

    // The language model ID to be used by this agent
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub model: Option<ModelId>,

    // Human-readable description of the agent's purpose
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub description: Option<String>,

    // Template for the system prompt provided to the agent
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub system_prompt: Option<Template<SystemContext>>,

    // Template for the user prompt provided to the agent
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub user_prompt: Option<Template<EventContext>>,

    /// When set to true all user events will also contain a suggestions field
    /// that is prefilled with the matching information from vector store.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub suggestions: Option<bool>,

    /// Suggests if the agent needs to maintain its state for the lifetime of
    /// the program.    
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub ephemeral: Option<bool>,

    /// Tools that the agent can use    
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub tools: Option<Vec<ToolName>>,

    // The transforms feature has been removed
    /// Used to specify the events the agent is interested in    
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = merge_subscription)]
    pub subscribe: Option<Vec<String>>,

    /// Maximum number of turns the agent can take    
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub max_turns: Option<u64>,

    /// Maximum depth to which the file walker should traverse for this agent
    /// If not provided, the maximum possible depth will be used
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub max_walker_depth: Option<usize>,

    /// Configuration for automatic context compaction
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub compact: Option<Compaction>,

    /// A set of custom rules that the agent should follow
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub custom_rules: Option<String>,
}

fn merge_subscription(base: &mut Option<Vec<String>>, other: Option<Vec<String>>) {
    if let Some(other) = other {
        if let Some(base) = base {
            base.extend(other);
        } else {
            *base = Some(other);
        }
    }
}

impl Agent {
    pub fn new(id: impl ToString) -> Self {
        Self {
            id: AgentId::new(id),
            disable: None,
            tool_supported: None,
            model: None,
            description: None,
            system_prompt: None,
            user_prompt: None,
            suggestions: None,
            ephemeral: None,
            tools: None,
            // transforms field removed
            subscribe: None,
            max_turns: None,
            max_walker_depth: None,
            compact: None,
            custom_rules: None,
            hide_content: None,
        }
    }

    pub fn tool_definition(&self) -> Result<ToolDefinition> {
        if self.description.is_none() || self.description.as_ref().is_none_or(|d| d.is_empty()) {
            return Err(Error::MissingAgentDescription(self.id.clone()));
        }
        Ok(ToolDefinition::new(self.id.as_str().to_string())
            .description(self.description.clone().unwrap()))
    }
}

impl Key for Agent {
    // Define the ID type for the Key trait implementation
    type Id = AgentId;

    // Return a reference to the agent's ID
    fn key(&self) -> &Self::Id {
        &self.id
    }
}

// The Transform enum has been removed

#[cfg(test)]
mod compaction_tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_compaction_should_compact() {
        // Test token threshold
        let compaction = Compaction::new(4000).token_threshold(6000 as usize);
        assert!(!compaction.should_compact(5000, 5, 10));
        assert!(compaction.should_compact(6000, 5, 10));
        assert!(compaction.should_compact(7000, 5, 10));

        // Test turn threshold
        let compaction = Compaction::new(4000).turn_threshold(10 as usize);
        assert!(!compaction.should_compact(5000, 9, 20));
        assert!(compaction.should_compact(5000, 10, 20));
        assert!(compaction.should_compact(5000, 11, 20));

        // Test message threshold
        let compaction = Compaction::new(4000).message_threshold(30 as usize);
        assert!(!compaction.should_compact(5000, 5, 29));
        assert!(compaction.should_compact(5000, 5, 30));
        assert!(compaction.should_compact(5000, 5, 31));

        // Test multiple thresholds - should compact when any threshold is exceeded
        let compaction = Compaction::new(4000)
            .token_threshold(6000 as usize)
            .turn_threshold(10 as usize)
            .message_threshold(30 as usize);

        assert!(!compaction.should_compact(5000, 5, 25)); // None exceeded
        assert!(compaction.should_compact(6000, 5, 25)); // Token exceeded
        assert!(compaction.should_compact(5000, 10, 25)); // Turn exceeded
        assert!(compaction.should_compact(5000, 5, 30)); // Message exceeded
    }

    #[test]
    fn test_merge_compact() {
        // Base has no value, should use other's value
        let mut base = Agent::new("Base"); // No compact set
        let other = Agent::new("Other").compact(
            Compaction::new(4000)
                .token_threshold(6000 as usize)
                .turn_threshold(10 as usize),
        );
        base.merge(other);

        let compact = base.compact.as_ref().unwrap();
        assert_eq!(compact.max_tokens, 4000);
        assert_eq!(compact.token_threshold, Some(6000));
        assert_eq!(compact.turn_threshold, Some(10));
        assert_eq!(compact.message_threshold, None);

        // Base has a value, should be overwritten by other
        let mut base =
            Agent::new("Base").compact(Compaction::new(3000).message_threshold(25 as usize));
        let other =
            Agent::new("Other").compact(Compaction::new(4000).token_threshold(6000 as usize));
        base.merge(other);

        let compact = base.compact.as_ref().unwrap();
        assert_eq!(compact.max_tokens, 4000);
        assert_eq!(compact.token_threshold, Some(6000));
        assert_eq!(compact.turn_threshold, None);
        assert_eq!(compact.message_threshold, None);
    }
    #[test]
    fn test_compaction_with_prompt() {
        // Test with custom prompt template
        let custom_prompt = "Conversation compacted: {{message_count}} messages ({{token_count}} tokens) reduced to {{kept_count}} messages";
        let compaction = Compaction::new(4000)
            .token_threshold(6000 as usize)
            .prompt(custom_prompt.to_string());

        assert_eq!(compaction.prompt, Some(custom_prompt.to_string()));

        // Test merging with prompt
        let mut base =
            Agent::new("Base").compact(Compaction::new(3000).message_threshold(25 as usize));

        let other = Agent::new("Other").compact(
            Compaction::new(4000)
                .token_threshold(6000 as usize)
                .prompt(custom_prompt.to_string()),
        );

        base.merge(other);

        let compact = base.compact.as_ref().unwrap();
        assert_eq!(compact.max_tokens, 4000);
        assert_eq!(compact.token_threshold, Some(6000));
        assert_eq!(compact.prompt, Some(custom_prompt.to_string()));
    }
    
    #[test]
    fn test_compaction_with_model() {
        // Test with model override
        let model_id = ModelId::new("gpt-3.5-turbo");
        let compaction = Compaction::new(4000)
            .token_threshold(6000 as usize)
            .model(model_id.clone());
        
        assert_eq!(compaction.model, Some(model_id.clone()));
        
        // Test merging with model
        let mut base = Agent::new("Base").compact(
            Compaction::new(3000).message_threshold(25 as usize)
        );
        
        let other = Agent::new("Other").compact(
            Compaction::new(4000)
                .token_threshold(6000 as usize)
                .model(model_id.clone())
        );
        
        base.merge(other);
        
        let compact = base.compact.as_ref().unwrap();
        assert_eq!(compact.model, Some(model_id));
    }
    
    #[test]
    fn test_compaction_with_empty_prompt() {
        // Default without a prompt
        let compaction = Compaction::new(4000).token_threshold(6000_usize);
        assert_eq!(compaction.prompt, None);

        // Adding a prompt
        let compaction = compaction.prompt("Custom prompt".to_string());
        assert_eq!(compaction.prompt, Some("Custom prompt".to_string()));

        // Test with empty string prompt (considered valid but will render as empty)
        let compaction = Compaction::new(4000).prompt("".to_string());
        assert_eq!(compaction.prompt, Some("".to_string()));
    }
}
#[cfg(test)]
mod hide_content_tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_merge_hide_content() {
        // Base has no value, other has value
        let mut base = Agent::new("Base"); // No hide_content set
        let other = Agent::new("Other").hide_content(true);
        base.merge(other);
        assert_eq!(base.hide_content, Some(true));

        // Base has a value, other has another value
        let mut base = Agent::new("Base").hide_content(false);
        let other = Agent::new("Other").hide_content(true);
        base.merge(other);
        assert_eq!(base.hide_content, Some(true));
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_merge_model() {
        // Base has a value, should not be overwritten
        let mut base = Agent::new("Base").model(ModelId::new("base"));
        let other = Agent::new("Other").model(ModelId::new("other"));
        base.merge(other);
        assert_eq!(base.model.unwrap(), ModelId::new("other"));

        // Base has no value, should take the other value
        let mut base = Agent::new("Base"); // No model
        let other = Agent::new("Other").model(ModelId::new("other"));
        base.merge(other);
        assert_eq!(base.model.unwrap(), ModelId::new("other"));
    }

    #[test]
    fn test_merge_tool_supported() {
        // Base has no value, should use other's value
        let mut base = Agent::new("Base"); // No tool_supported set
        let other = Agent::new("Other").tool_supported(true);
        base.merge(other);
        assert_eq!(base.tool_supported, Some(true));

        // Base has a value, should not be overwritten
        let mut base = Agent::new("Base").tool_supported(false);
        let other = Agent::new("Other").tool_supported(true);
        base.merge(other);
        assert_eq!(base.tool_supported, Some(true));
    }

    #[test]
    fn test_merge_disable() {
        // Base has no value, should use other's value
        let mut base = Agent::new("Base"); // No disable set
        let other = Agent::new("Other").disable(true);
        base.merge(other);
        assert_eq!(base.disable, Some(true));

        // Base has a value, should be overwritten
        let mut base = Agent::new("Base").disable(false);
        let other = Agent::new("Other").disable(true);
        base.merge(other);
        assert_eq!(base.disable, Some(true));
    }

    #[test]
    fn test_merge_bool_flags() {
        // With the option strategy, the first value is preserved
        let mut base = Agent::new("Base").suggestions(true);
        let other = Agent::new("Other").suggestions(false);
        base.merge(other);
        assert_eq!(base.suggestions, Some(false));

        // Now test with no initial value
        let mut base = Agent::new("Base"); // no suggestions set
        let other = Agent::new("Other").suggestions(false);
        base.merge(other);
        assert_eq!(base.suggestions, Some(false));

        // Test ephemeral flag with option strategy
        let mut base = Agent::new("Base").ephemeral(true);
        let other = Agent::new("Other").ephemeral(false);
        base.merge(other);
        assert_eq!(base.ephemeral, Some(false));
    }

    #[test]
    fn test_merge_tools() {
        // Base has no value, should take other's values
        let mut base = Agent::new("Base"); // no tools
        let other = Agent::new("Other").tools(vec![ToolName::new("tool2"), ToolName::new("tool3")]);
        base.merge(other);

        // Should contain all tools from the other agent
        let tools = base.tools.as_ref().unwrap();
        assert_eq!(tools.len(), 2);
        assert!(tools.contains(&ToolName::new("tool2")));
        assert!(tools.contains(&ToolName::new("tool3")));

        // Base has a value, should not be overwritten
        let mut base =
            Agent::new("Base").tools(vec![ToolName::new("tool1"), ToolName::new("tool2")]);
        let other = Agent::new("Other").tools(vec![ToolName::new("tool3"), ToolName::new("tool4")]);
        base.merge(other);

        // Should have other's tools
        let tools = base.tools.as_ref().unwrap();
        assert_eq!(tools.len(), 2);
        assert!(tools.contains(&ToolName::new("tool3")));
        assert!(tools.contains(&ToolName::new("tool4")));
    }

    // test_merge_transforms has been removed as the transform feature is no longer
    // supported

    #[test]
    fn test_merge_subscribe() {
        // Base has no value, should take other's values
        let mut base = Agent::new("Base"); // no subscribe
        let other = Agent::new("Other").subscribe(vec!["event2".to_string(), "event3".to_string()]);
        base.merge(other);

        // Should contain events from other
        let subscribe = base.subscribe.as_ref().unwrap();
        assert_eq!(subscribe.len(), 2);
        assert!(subscribe.contains(&"event2".to_string()));
        assert!(subscribe.contains(&"event3".to_string()));

        // Base has a value, should not be overwritten
        let mut base =
            Agent::new("Base").subscribe(vec!["event1".to_string(), "event2".to_string()]);
        let other = Agent::new("Other").subscribe(vec!["event3".to_string(), "event4".to_string()]);
        base.merge(other);

        // Should have other's events
        let subscribe = base.subscribe.as_ref().unwrap();
        assert_eq!(subscribe.len(), 4);
        assert!(subscribe.contains(&"event1".to_string()));
        assert!(subscribe.contains(&"event2".to_string()));
        assert!(subscribe.contains(&"event3".to_string()));
        assert!(subscribe.contains(&"event4".to_string()));
    }
}