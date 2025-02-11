use derive_builder::Builder;
use derive_more::derive::Display;
use derive_setters::Setters;
use schemars::schema_for;
use serde::{Deserialize, Serialize};

use crate::prompt::Prompt;
use crate::variables::Variables;
use crate::{Environment, ModelId, ToolDefinition, ToolName};

#[derive(Default, Setters, Clone, Serialize, Deserialize)]
#[setters(strip_option)]
pub struct SystemContext {
    pub env: Option<Environment>,
    pub tool_information: Option<String>,
    pub tool_supported: Option<bool>,
    pub custom_instructions: Option<String>,
    pub files: Vec<String>,
}

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone, Serialize, Deserialize)]
#[serde(transparent)]
pub struct AgentId(String);
impl AgentId {
    pub fn new(id: impl ToString) -> Self {
        Self(id.to_string())
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<ToolName> for AgentId {
    fn from(value: ToolName) -> Self {
        Self(value.into_string())
    }
}

#[derive(Clone, Serialize, Deserialize, Builder)]
#[builder(setter(into))]
pub struct Agent {
    pub id: AgentId,
    pub model: ModelId,
    pub description: String,
    pub system_prompt: Prompt<SystemContext>,
    pub user_prompt: Prompt<Variables>,

    /// Suggests if the agent needs to maintain its state for the lifetime of
    /// the program.
    #[builder(default)]
    pub ephemeral: bool,

    /// Tools that the agent can use
    #[builder(default)]
    pub tools: Vec<ToolName>,

    #[builder(default)]
    pub transforms: Vec<Transform>,

    /// Downstream agents that this agent can handover to
    #[builder(default)]
    pub handovers: Vec<Downstream>,

    /// Represents that the agent is the entry point to the workflow
    #[builder(default = true)]
    pub entry: bool,
}

impl From<Agent> for ToolDefinition {
    fn from(value: Agent) -> Self {
        ToolDefinition {
            name: ToolName::new(value.id.0),
            description: value.description,
            input_schema: schema_for!(Variables),
            output_schema: None,
        }
    }
}

/// Transformations that can be applied to the agent's context before sending it
/// upstream to the provider.
#[derive(Clone, Serialize, Deserialize)]
pub enum Transform {
    /// Compresses multiple assistant messages into a single message
    Assistant {
        input: String,
        output: String,
        agent_id: AgentId,
        token_limit: usize,
    },

    /// Works on the user prompt by enriching it with additional information
    User {
        agent_id: AgentId,
        input: String,
        output: String,
    },

    /// Intercepts the context and performs an operation without changing the
    /// context
    Tap { agent_id: AgentId, input: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Downstream {
    pub agent: AgentId,
    pub wait: bool,
}
