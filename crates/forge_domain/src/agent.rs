use derive_more::derive::Display;
use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::merge::Key;
use crate::template::Template;
use crate::{
    Context, Error, EventContext, ModelId, Result, Role, SystemContext, ToolDefinition, ToolName,
};

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
pub struct Compact {
    /// Number of most recent messages to preserve during compaction
    /// These messages won't be considered for summarization
    #[serde(default = "default_preserve_count")]
    #[merge(strategy = crate::merge::std::overwrite)]
    pub retention_window: usize,
    /// Maximum number of tokens to keep after compaction
    #[merge(strategy = crate::merge::option)]
    pub max_tokens: Option<usize>,

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

    /// Model ID to use for compaction, useful when compacting with a
    /// cheaper/faster model
    #[merge(strategy = crate::merge::std::overwrite)]
    pub model: ModelId,
    /// Optional tag name to extract content from when summarizing (e.g.,
    /// "summary")
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub summary_tag: Option<String>,
}

/// Default number of messages to preserve during compaction
fn default_preserve_count() -> usize {
    6
}

impl Compact {
    /// Creates a new compaction configuration with the specified maximum token
    /// limit
    pub fn new(model: ModelId) -> Self {
        Self {
            max_tokens: None,
            token_threshold: None,
            turn_threshold: None,
            message_threshold: None,
            prompt: None,
            summary_tag: None,
            model,
            retention_window: default_preserve_count(),
        }
    }

    /// Determines if compaction should be triggered based on the current
    /// context
    pub fn should_compact(&self, context: &Context) -> bool {
        // Check if any of the thresholds have been exceeded
        if let Some(token_threshold) = self.token_threshold {
            // Use the context's text representation to estimate token count
            let token_count = estimate_token_count(&context.to_text());
            if token_count >= token_threshold {
                return true;
            }
        }

        if let Some(turn_threshold) = self.turn_threshold {
            if context
                .messages
                .iter()
                .filter(|message| message.has_role(Role::User))
                .count()
                >= turn_threshold
            {
                return true;
            }
        }

        if let Some(message_threshold) = self.message_threshold {
            // Count messages directly from context
            let msg_count = context.messages.len();
            if msg_count >= message_threshold {
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
    pub compact: Option<Compact>,

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

/// Estimates the token count from a string representation
/// This is a simple estimation that should be replaced with a more accurate
/// tokenizer
fn estimate_token_count(text: &str) -> usize {
    // A very rough estimation that assumes ~4 characters per token on average
    // In a real implementation, this should use a proper LLM-specific tokenizer
    text.len() / 4
}

// The Transform enum has been removed
