use std::fmt;
use std::marker::PhantomData;
use std::path::PathBuf;

use async_trait::async_trait;
use derive_setters::Setters;
use handlebars::Handlebars;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::error::Result;

/// Represents the contents of a prompt, which can either be direct text or a
/// file reference
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum PromptContent {
    Text(String),
    File(PathBuf),
}

impl From<String> for PromptContent {
    fn from(s: String) -> Self {
        PromptContent::Text(s)
    }
}

impl From<&str> for PromptContent {
    fn from(s: &str) -> Self {
        PromptContent::Text(s.to_string())
    }
}

impl From<PathBuf> for PromptContent {
    fn from(p: PathBuf) -> Self {
        PromptContent::File(p)
    }
}

impl fmt::Display for PromptContent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PromptContent::Text(content) => write!(f, "{}", content),
            PromptContent::File(path) => write!(f, "@{}", path.display()),
        }
    }
}

impl PromptContent {
    pub fn new(content: impl Into<String>) -> Self {
        PromptContent::Text(content.into())
    }

    pub fn from_file<P: AsRef<std::path::Path>>(path: P) -> Self {
        PromptContent::File(path.as_ref().to_path_buf())
    }
}

/// Represents an AI agent with specific system and user prompts, templated with
/// a context type
#[derive(Clone, Debug, Default, Deserialize, Serialize, Setters)]
#[serde(rename_all = "camelCase")]
#[setters(into, strip_option)]
pub struct Agent<C> {
    /// Name of the agent
    pub name: String,

    /// Description of what the agent does
    #[serde(rename = "description", skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    /// The system prompt that defines the agent's behavior
    #[serde(rename = "systemPrompt", skip_serializing_if = "Option::is_none")]
    pub system_prompt: Option<PromptContent>,

    /// Optional user prompt template for consistent interactions
    #[serde(rename = "userPrompt", skip_serializing_if = "Option::is_none")]
    pub user_prompt: Option<PromptContent>,

    /// Phantom data for the context type
    #[serde(skip)]
    _context: PhantomData<C>,
}

impl<C> Agent<C>
where
    C: Serialize + DeserializeOwned,
{
    /// Creates a new agent
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: None,
            system_prompt: None,
            user_prompt: None,
            _context: PhantomData,
        }
    }

    /// Renders the system prompt with the given context if it exists
    pub fn render_system_prompt(&self, context: &C) -> Result<Option<String>> {
        if let Some(system_prompt) = &self.system_prompt {
            let handlebars = Handlebars::new();
            let prompt = system_prompt.to_string();
            Ok(Some(handlebars.render_template(&prompt, context)?))
        } else {
            Ok(None)
        }
    }

    /// Renders the user prompt with the given context if it exists
    pub fn render_user_prompt(&self, context: &C) -> Result<Option<String>> {
        if let Some(user_prompt) = &self.user_prompt {
            let handlebars = Handlebars::new();
            let prompt = user_prompt.to_string();
            Ok(Some(handlebars.render_template(&prompt, context)?))
        } else {
            Ok(None)
        }
    }
}

/// Loader trait for loading Agent definitions. The loader should be able to
/// load all available agents from a source (e.g., configuration files).
#[async_trait]
pub trait AgentLoader<C>
where
    C: Send + Sync + DeserializeOwned,
{
    /// Load all available agents. Returns a Vec of agents in the order they
    /// were defined in the source.
    async fn load_agents(&self) -> anyhow::Result<Vec<Agent<C>>>;
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde::Deserialize;

    use super::*;

    #[derive(Debug, Serialize, Deserialize)]
    struct CodeContext {
        role: String,
        language: String,
    }

    use std::path::Path;

    #[test]
    fn test_create_agent() {
        let agent: Agent<CodeContext> = Agent::new("Coder");

        assert_eq!(agent.name, "Coder");
        assert_eq!(agent.description, None);
        assert_eq!(agent.system_prompt, None);
        assert_eq!(agent.user_prompt, None);
    }

    #[test]
    fn test_create_with_prompts() {
        let agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt("You are a helpful coding assistant");

        assert_eq!(agent.name, "Coder");
        assert_eq!(agent.description, Some("A coding assistant".to_string()));
        assert_eq!(
            agent.system_prompt,
            Some(PromptContent::Text(
                "You are a helpful coding assistant".to_string()
            ))
        );
        assert_eq!(agent.user_prompt, None);
    }

    #[test]
    fn test_agent_with_file_prompts() {
        let agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt(PromptContent::from_file("prompts/system.md"))
            .user_prompt(PromptContent::from_file("prompts/user.md"));

        assert_eq!(
            agent.system_prompt,
            Some(PromptContent::File(
                Path::new("prompts/system.md").to_path_buf()
            ))
        );
        assert_eq!(
            agent.user_prompt,
            Some(PromptContent::File(
                Path::new("prompts/user.md").to_path_buf()
            ))
        );
    }

    #[test]
    fn test_render_prompts_with_context() {
        let agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt("You are a {{role}} coding assistant")
            .user_prompt("How can I help with {{language}} code today?");

        let context = CodeContext { role: "helpful".to_string(), language: "Rust".to_string() };

        assert_eq!(
            agent.render_system_prompt(&context).unwrap(),
            Some("You are a helpful coding assistant".to_string())
        );
        assert_eq!(
            agent.render_user_prompt(&context).unwrap(),
            Some("How can I help with Rust code today?".to_string())
        );
    }

    #[test]
    fn test_agent_json_format() {
        // Test full agent with all fields
        let full_agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt(PromptContent::Text(
                "You are a helpful coding assistant".to_string(),
            ))
            .user_prompt("How can I help?");

        insta::assert_json_snapshot!(full_agent);

        // Test minimal agent (only name)
        let minimal_agent: Agent<CodeContext> = Agent::new("Coder");

        insta::assert_json_snapshot!(minimal_agent);

        // Test agent with file prompts
        let file_agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt(PromptContent::from_file("prompts/system.md"))
            .user_prompt(PromptContent::from_file("prompts/user.md"));

        insta::assert_json_snapshot!(file_agent);
    }

    #[test]
    fn test_agent_roundtrip() {
        let agent: Agent<CodeContext> = Agent::new("Coder")
            .description("A coding assistant")
            .system_prompt(PromptContent::Text("System prompt".to_string()))
            .user_prompt("User prompt");

        let serialized = serde_json::to_string(&agent).unwrap();
        let deserialized: Agent<CodeContext> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(deserialized.name, agent.name);
        assert_eq!(deserialized.description, agent.description);
        assert_eq!(deserialized.system_prompt, agent.system_prompt);
        assert_eq!(deserialized.user_prompt, agent.user_prompt);
    }
}
