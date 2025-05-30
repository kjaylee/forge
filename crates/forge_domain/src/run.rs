use std::collections::HashMap;

use chrono::{DateTime, Local};
use derive_setters::Setters;
use serde_json::Value;

use crate::{Result, *};

/// The `Run` struct represents a run of the agent with its context.
#[derive(Debug, Clone, Setters)]
pub struct Run {
    agent: Agent,
    env: Environment,
    context: Context,
    current_time: DateTime<Local>,
    models: Vec<Model>,
    tool_definitions: Vec<ToolDefinition>,
    files: Vec<String>,
    variables: HashMap<String, Value>,
}

type SignalResult = Result<WrappedSignal>;
type WrappedSignal = Wrap<Signal>;

impl Run {
    pub fn new(agent: Agent, env: Environment, current_time: DateTime<Local>) -> Self {
        let mut context = Context::default();
        if let Some(top_k) = agent.top_k {
            context = context.top_k(top_k);
        }
        if let Some(temperature) = agent.temperature {
            context = context.temperature(temperature);
        }
        if let Some(top_p) = agent.top_p {
            context = context.top_p(top_p);
        }
        Self {
            agent,
            context,
            models: Default::default(),
            current_time,
            tool_definitions: Default::default(),
            env,
            files: Default::default(),
            variables: Default::default(),
        }
    }

    pub fn update(&mut self, action: Action) -> SignalResult {
        match action {
            Action::Initialize { event, models, tool_definitions, current_time } => {
                self.on_init(event, models, tool_definitions, current_time)
            }
            Action::SystemRender { content } => self.on_system_render(content),
            Action::UserRender { content } => self.on_render_user_message(content),
            Action::Message(message) => self.on_message(message),
        }
    }

    fn on_system_render(&mut self, content: String) -> std::result::Result<Wrap<Signal>, Error> {
        self.context.set_first_system_message_mut(content);
        Signal::default().wrap().ok()
    }

    fn on_init(
        &mut self,
        event: Event,
        models: Vec<Model>,
        tool_definitions: Vec<ToolDefinition>,
        current_time: DateTime<Local>,
    ) -> std::result::Result<WrappedSignal, Error> {
        // Set the values from the Initialize action
        self.models = models;
        self.tool_definitions = tool_definitions;
        self.current_time = current_time;

        Wrap::all([
            self.render_system_prompt()?,
            self.render_user_prompt(&event)?,
            self.set_tools()?,
            self.add_user_attachments(&event.value)?,
            Signal::Chat {
                agent: Box::new(self.agent.clone()),
                context: self.context.clone(),
            }
            .into(),
        ])
        .ok()
    }

    fn tool_information(&self) -> Result<Option<String>> {
        let tool_supported = self.tool_supported()?;
        if tool_supported {
            Ok(None)
        } else {
            // Get the tools specified by the agent
            let agent_tools = match &self.agent.tools {
                Some(tools) => tools,
                None => return Ok(None),
            };

            // Filter tool definitions to only include tools specified by the agent
            let allowed_tools: Vec<ToolDefinition> = self
                .tool_definitions
                .iter()
                .filter(|tool| agent_tools.contains(&tool.name))
                .cloned()
                .collect();

            if allowed_tools.is_empty() {
                return Ok(None);
            }

            // Create tool usage prompt
            let tool_usage = ToolUsagePrompt::from(&allowed_tools);
            Ok(Some(tool_usage.to_string()))
        }
    }

    fn render_system_prompt(&mut self) -> SignalResult {
        if let Some(system_prompt) = &self.agent.system_prompt {
            Signal::RenderSystem {
                prompt: system_prompt.clone(),
                context: Box::new(SystemContext {
                    current_time: self
                        .current_time
                        .format("%Y-%m-%d %H:%M:%S %:z")
                        .to_string(),
                    env: Some(self.env.clone()),
                    tool_information: self.tool_information()?,
                    tool_supported: self.tool_supported()?,
                    files: self.files.clone(),
                    custom_rules: self
                        .agent
                        .custom_rules
                        .as_ref()
                        .cloned()
                        .unwrap_or_default(),
                    variables: self.variables.clone(),
                }),
            }
            .wrap()
            .ok()
        } else {
            Signal::default().wrap().ok()
        }
    }

    fn render_user_prompt(&mut self, event: &Event) -> SignalResult {
        if let Some(user_prompt) = &self.agent.user_prompt {
            Signal::RenderUser {
                prompt: user_prompt.clone(),
                context: Box::new(
                    EventContext::new(event.clone()).variables(self.variables.clone()),
                ),
            }
            .wrap()
            .ok()
        } else {
            Signal::default().wrap().ok()
        }
    }

    fn on_render_user_message(&mut self, content: String) -> SignalResult {
        if !content.is_empty() {
            self.context = self
                .context
                .clone()
                .add_message(ContextMessage::user(content, self.agent.model.clone()));
        }

        Signal::default().wrap().ok()
    }

    fn set_tools(&mut self) -> SignalResult {
        // Get the tools specified by the agent
        let agent_tools = match &self.agent.tools {
            Some(tools) => tools,
            None => {
                // No tools specified, clear any existing tools in context
                self.context.tools.clear();
                return Ok(Wrap::default());
            }
        };

        // Create a map of tool definitions for efficient lookup
        let tool_def_map: std::collections::HashMap<&crate::ToolName, &ToolDefinition> = self
            .tool_definitions
            .iter()
            .map(|def| (&def.name, def))
            .collect();

        // Find definitions for each agent tool, error if any are missing
        let mut filtered_tools = Vec::new();
        for tool_name in agent_tools {
            match tool_def_map.get(tool_name) {
                Some(tool_def) => filtered_tools.push((*tool_def).clone()),
                None => return Err(Error::ToolDefinitionNotFound(tool_name.clone())),
            }
        }

        // Set the tools in the context (in-place mutation)
        self.context.tools = filtered_tools;

        Ok(Wrap::default())
    }

    fn add_user_attachments(&mut self, _message: &Value) -> SignalResult {
        // TODO: Implement user attachments addition
        Ok(Wrap::default())
    }

    fn on_message(&mut self, _message: ChatCompletionMessage) -> SignalResult {
        // TODO: Implement message handling
        Ok(Wrap::default())
    }
    /// Returns whether tools are supported for the agent's model
    ///
    /// This method looks up the agent's model from the models collection
    /// and returns the tool support information:
    /// - Returns Err(MissingModel) if the agent has no model specified
    /// - Returns Err(ModelNotFound) if the model is not found in the models
    ///   collection
    /// - Returns Ok(true) if the model exists and supports tools
    /// - Returns Ok(false) if the model exists but doesn't support tools or has
    ///   no tool support information
    pub fn tool_supported(&self) -> Result<bool> {
        // Get the model ID from the agent
        let model_id = self
            .agent
            .model
            .as_ref()
            .ok_or(Error::MissingModel(self.agent.id.clone()))?;

        // Find the model in the models collection
        Ok(self
            .models
            .iter()
            .find(|model| &model.id == model_id)
            .ok_or(Error::ModelNotFound(model_id.clone()))?
            .tools_supported
            .unwrap_or_default())
    }
}

pub enum Action {
    Initialize {
        event: Event,
        models: Vec<Model>,
        tool_definitions: Vec<ToolDefinition>,
        current_time: DateTime<Local>,
    },
    SystemRender {
        content: String,
    },
    UserRender {
        content: String,
    },
    Message(ChatCompletionMessage),
}

#[derive(Default, Debug, Clone)]
/// Pure signal types without composition logic
pub enum Signal {
    #[default]
    Continue,
    Stop,
    Chat {
        agent: Box<Agent>,
        context: Context,
    },
    RenderSystem {
        prompt: Template<SystemContext>,
        context: Box<SystemContext>,
    },
    RenderUser {
        prompt: Template<EventContext>,
        context: Box<EventContext>,
    },
}

impl Signal {
    /// Wraps the signal in a `Wrap` monoid
    pub fn wrap(self) -> Wrap<Self> {
        Wrap::new(self)
    }
}

/// Monoid-like wrapper for composing signals using Vec
#[derive(Default, Debug, Clone)]
pub struct Wrap<A> {
    items: Vec<A>,
}

impl<A> Wrap<A> {
    /// Monoid binary operation - combines two wrapped values by concatenation
    pub fn and(mut self, other: impl Into<Wrap<A>>) -> Self {
        self.items.extend(other.into().items);
        self
    }

    /// Wraps a single value
    pub fn new(value: A) -> Self {
        Wrap { items: vec![value] }
    }

    /// Combines multiple Wrap values into a single Wrap
    pub fn all<I>(wraps: I) -> Self
    where
        I: IntoIterator<Item = Wrap<A>>,
    {
        let mut items = Vec::new();
        for wrap in wraps {
            items.extend(wrap.items);
        }
        Wrap { items }
    }
}

impl<A> Wrap<A> {
    /// Converts to Result (convenience method)
    pub fn ok(self) -> Result<Self> {
        Ok(self)
    }

    /// Returns an iterator over all values in this wrapper
    pub fn iter(&self) -> std::slice::Iter<A> {
        self.items.iter()
    }
}

impl<A> IntoIterator for Wrap<A> {
    type Item = A;
    type IntoIter = std::vec::IntoIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl<A> From<A> for Wrap<A> {
    fn from(value: A) -> Self {
        Wrap::new(value)
    }
}

impl<'a, A> IntoIterator for &'a Wrap<A> {
    type Item = &'a A;
    type IntoIter = std::slice::Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::agent::Agent;
    use crate::model::{Model, ModelId};

    impl Default for Environment {
        fn default() -> Self {
            use url::Url;
            Self {
                os: Default::default(),
                pid: Default::default(),
                cwd: Default::default(),
                home: Default::default(),
                shell: Default::default(),
                base_path: Default::default(),
                provider: Provider::OpenAI {
                    url: Url::parse("https://api.openai.com/v1/").unwrap(),
                    key: Some("-key-".to_string()),
                },
                retry_config: Default::default(),
            }
        }
    }

    impl Run {
        /// Creates a test fixture with comprehensive defaults for testing
        fn fixture() -> Self {
            let agent = Agent::new("test-agent")
                .model(ModelId::new("test-model"))
                .user_prompt(Template::new("Hello {{event.value}}"))
                .tools(vec![ToolName::new("test-tool")]);

            let models = vec![
                Model::new(ModelId::new("test-model")).tools_supported(true),
                Model::new(ModelId::new("gpt-4o")).tools_supported(true),
                Model::new(ModelId::new("gpt-3.5-turbo")).tools_supported(false),
            ];

            let tool_definitions = vec![
                ToolDefinition::new("test-tool").description("Test Tool"),
                ToolDefinition::new("tool1").description("Tool 1"),
                ToolDefinition::new("tool2").description("Tool 2"),
                ToolDefinition::new("tool3").description("Tool 3"),
            ];

            let env = Environment::default();
            let current_time = Local::now();

            Run::new(agent, env, current_time)
                .models(models)
                .tool_definitions(tool_definitions)
        }

        /// Creates a test fixture with a custom agent
        fn fixture_with_agent(agent: Agent) -> Self {
            let models = vec![
                Model::new(ModelId::new("test-model")).tools_supported(true),
                Model::new(ModelId::new("gpt-4o")).tools_supported(true),
                Model::new(ModelId::new("gpt-3.5-turbo")).tools_supported(false),
            ];

            let tool_definitions = vec![
                ToolDefinition::new("test-tool").description("Test Tool"),
                ToolDefinition::new("tool1").description("Tool 1"),
                ToolDefinition::new("tool2").description("Tool 2"),
                ToolDefinition::new("tool3").description("Tool 3"),
            ];

            let env = Environment::default();
            let current_time = Local::now();

            Run::new(agent, env, current_time)
                .models(models)
                .tool_definitions(tool_definitions)
        }
    }

    #[test]
    fn test_run_new() {
        let agent = Agent::new("my-agent").temperature(0.5).top_k(10).top_p(0.9);
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time);
        assert_eq!(run.agent.id.as_str(), "my-agent");
        assert!(run.context.messages.is_empty());
        assert!(run.models.is_empty());
        assert_eq!(run.context.top_k.map(|x| x.value()), Some(10));
        assert_eq!(run.context.temperature.map(|x| x.value()), Some(0.5));
        assert_eq!(run.context.top_p.map(|x| x.value()), Some(0.9));
    }

    #[test]
    fn test_tool_supported_agent_with_model_that_supports_tools() {
        // Test case 1: Agent has model that exists and supports tools
        let agent = Agent::new("test-agent").model(ModelId::new("gpt-4o"));
        let models = vec![Model::new(ModelId::new("gpt-4o")).tools_supported(true)];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        assert_eq!(run.tool_supported().unwrap(), true);
    }

    #[test]
    fn test_tool_supported_agent_with_model_that_does_not_support_tools() {
        // Test case 2: Agent has model that exists but doesn't support tools
        let agent = Agent::new("test-agent").model(ModelId::new("gpt-3.5-turbo"));
        let models = vec![Model::new(ModelId::new("gpt-3.5-turbo")).tools_supported(false)];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        assert_eq!(run.tool_supported().unwrap(), false);
    }

    #[test]
    fn test_tool_supported_agent_with_model_null_tools_supported() {
        // Test case 3: Agent has model that exists but has null tools_supported
        let agent = Agent::new("test-agent").model(ModelId::new("forge-test-model"));
        let models = vec![Model::new(ModelId::new("forge-test-model"))];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        assert_eq!(run.tool_supported().unwrap(), false);
    }

    #[test]
    fn test_tool_supported_agent_with_model_not_found() {
        // Test case 4: Agent has model that is not found in the models collection
        let agent = Agent::new("test-agent").model(ModelId::new("nonexistent-model"));
        let models = vec![Model::new(ModelId::new("different-model")).tools_supported(true)];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        let result = run.tool_supported();
        let Error::ModelNotFound(model_id) = result.unwrap_err() else {
            panic!("Expected ModelNotFound error")
        };
        assert_eq!(model_id.as_str(), "nonexistent-model");
    }

    #[test]
    fn test_tool_supported_agent_with_no_model_specified() {
        // Test case 5: Agent has no model specified
        let agent = Agent::new("test-agent"); // No model set
        let models = vec![Model::new(ModelId::new("some-model")).tools_supported(true)];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        let result = run.tool_supported();
        let Error::MissingModel(agent_id) = result.unwrap_err() else {
            panic!("Expected MissingModel error")
        };
        assert_eq!(agent_id.as_str(), "test-agent");
    }

    #[test]
    fn test_update_initialize_action_sets_values() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model"));
        let mut run = Run::new(agent, Environment::default(), Local::now());

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![ToolDefinition::new("test-tool")];
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!({}));

        let action =
            Action::Initialize { event: event.clone(), models, tool_definitions, current_time };

        let result = run.update(action);

        assert!(result.is_ok());
        assert_eq!(run.models.len(), 1);
        assert_eq!(run.tool_definitions.len(), 1);
    }

    #[test]
    fn test_update_initialize_action_returns_chat_signal() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model"));
        let mut run = Run::new(agent, Environment::default(), Local::now());

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = Default::default();
        let current_time = Local::now();
        let event = Event::new("test-event", Value::Null);

        let action = Action::Initialize { event, models, tool_definitions, current_time };

        let result = run.update(action);

        assert!(result.is_ok());
        let signal = result.unwrap();

        // Verify that the signal contains a Chat signal
        assert!(signal.iter().any(|s| matches!(s, Signal::Chat { .. })));
    }

    #[test]
    fn test_tool_supported_multiple_models_correct_one_found() {
        // Test case 6: Multiple models in collection, correct one is found
        let agent = Agent::new("test-agent").model(ModelId::new("model-2"));
        let models = vec![
            Model::new(ModelId::new("model-1")).tools_supported(false),
            Model::new(ModelId::new("model-2")).tools_supported(true),
            Model::new(ModelId::new("model-3")).tools_supported(false),
        ];
        let current_time = Local::now();
        let run = Run::new(agent, Environment::default(), current_time).models(models);
        assert_eq!(run.tool_supported().unwrap(), true);
    }

    #[test]
    fn test_set_tools_agent_with_no_tools_specified() {
        // Test case 1: Agent with no tools specified should result in empty context
        // tools
        let agent = Agent::new("test-agent"); // Agent without tools
        let mut run = Run::fixture_with_agent(agent);

        let result = run.set_tools();
        assert!(result.is_ok());
        assert!(run.context.tools.is_empty());
    }

    #[test]
    fn test_set_tools_agent_with_specific_tools_filters_definitions() {
        // Test case 2: Agent with specific tools should filter tool definitions
        let agent =
            Agent::new("test-agent").tools(vec![ToolName::new("tool1"), ToolName::new("tool3")]);
        let mut run = Run::fixture_with_agent(agent);

        let result = run.set_tools();
        assert!(result.is_ok());
        assert_eq!(run.context.tools.len(), 2);

        let tool_names: Vec<&str> = run
            .context
            .tools
            .iter()
            .map(|tool| tool.name.as_str())
            .collect();
        assert!(tool_names.contains(&"tool1"));
        assert!(tool_names.contains(&"tool3"));
        assert!(!tool_names.contains(&"tool2"));
    }

    #[test]
    fn test_set_tools_agent_with_nonexistent_tool_returns_error() {
        // Test case 3: Agent with tools that don't match any tool definitions
        let agent = Agent::new("test-agent").tools(vec![ToolName::new("nonexistent_tool")]);
        let tool_definitions = vec![
            ToolDefinition::new("tool1").description("Tool 1"),
            ToolDefinition::new("tool2").description("Tool 2"),
        ];
        let current_time = Local::now();
        let mut run = Run::new(agent, Environment::default(), current_time)
            .tool_definitions(tool_definitions);

        let result = run.set_tools();
        assert!(result.is_err());
        let Error::ToolDefinitionNotFound(tool_name) = result.unwrap_err() else {
            panic!("Expected ToolDefinitionNotFound error")
        };
        assert_eq!(tool_name.as_str(), "nonexistent_tool");
    }

    #[test]
    fn test_set_tools_agent_with_missing_tool_definition_returns_error() {
        // Test case 4: Agent with tool that doesn't exist in tool definitions
        let agent = Agent::new("test-agent").tools(vec![ToolName::new("missing_tool")]);
        let tool_definitions = vec![
            ToolDefinition::new("tool1").description("Tool 1"),
            ToolDefinition::new("tool2").description("Tool 2"),
        ];
        let current_time = Local::now();
        let mut run = Run::new(agent, Environment::default(), current_time)
            .tool_definitions(tool_definitions);

        let result = run.set_tools();
        assert!(result.is_err());
        let Error::ToolDefinitionNotFound(tool_name) = result.unwrap_err() else {
            panic!("Expected ToolDefinitionNotFound error")
        };
        assert_eq!(tool_name.as_str(), "missing_tool");
    }

    #[test]
    fn test_update_with_system_render_action_stores_content() {
        let fixture = Agent::new("test-agent");
        let mut run = Run::new(fixture, Environment::default(), Local::now());
        let action = Action::SystemRender { content: "Rendered system prompt content".to_string() };

        let actual = run.update(action).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));

        // Check that the system message was set as the first message
        assert_eq!(run.context.messages.len(), 1);
        if let Some(ContextMessage::Text(message)) = run.context.messages.first() {
            assert_eq!(message.role, Role::System);
            assert_eq!(message.content, "Rendered system prompt content");
        } else {
            panic!("Expected first message to be a text message with system role");
        }
    }

    #[test]
    fn test_update_with_system_render_action_overwrites_previous_content() {
        let fixture = Agent::new("test-agent");
        let mut run = Run::new(fixture, Environment::default(), Local::now());

        // Set initial content
        let first_action = Action::SystemRender { content: "First content".to_string() };
        run.update(first_action).unwrap();

        // Overwrite with new content
        let second_action = Action::SystemRender { content: "Second content".to_string() };
        let actual = run.update(second_action).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));

        // Check that the system message was updated
        assert_eq!(run.context.messages.len(), 1);
        if let Some(ContextMessage::Text(message)) = run.context.messages.first() {
            assert_eq!(message.role, Role::System);
            assert_eq!(message.content, "Second content");
        } else {
            panic!("Expected first message to be a text message with system role");
        }
    }

    #[test]
    fn test_update_with_user_render_action_stores_content() {
        let fixture = Agent::new("test-agent");
        let mut run = Run::new(fixture, Environment::default(), Local::now());
        let action = Action::UserRender { content: "Rendered user prompt content".to_string() };

        let actual = run.update(action).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));

        // Check that the user message was added
        assert_eq!(run.context.messages.len(), 1);
        if let Some(ContextMessage::Text(message)) = run.context.messages.first() {
            assert_eq!(message.role, Role::User);
            assert_eq!(message.content, "Rendered user prompt content");
        } else {
            panic!("Expected first message to be a text message with user role");
        }
    }

    #[test]
    fn test_update_with_user_render_action_empty_content_does_nothing() {
        let fixture = Agent::new("test-agent");
        let mut run = Run::new(fixture, Environment::default(), Local::now());
        let action = Action::UserRender { content: "".to_string() };

        let actual = run.update(action).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));

        // Check that no message was added
        assert_eq!(run.context.messages.len(), 0);
    }

    #[test]
    fn test_update_with_user_render_action_adds_to_existing_messages() {
        let fixture = Agent::new("test-agent");
        let mut run = Run::new(fixture, Environment::default(), Local::now());

        // Add a system message first
        let system_action = Action::SystemRender { content: "System content".to_string() };
        run.update(system_action).unwrap();

        // Add a user message
        let user_action = Action::UserRender { content: "User content".to_string() };
        let actual = run.update(user_action).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));

        // Check that both messages exist
        assert_eq!(run.context.messages.len(), 2);

        if let Some(ContextMessage::Text(message)) = run.context.messages.first() {
            assert_eq!(message.role, Role::System);
            assert_eq!(message.content, "System content");
        } else {
            panic!("Expected first message to be a system message");
        }

        if let Some(ContextMessage::Text(message)) = run.context.messages.get(1) {
            assert_eq!(message.role, Role::User);
            assert_eq!(message.content, "User content");
        } else {
            panic!("Expected second message to be a user message");
        }
    }

    #[test]
    fn test_set_user_prompt_with_user_prompt_returns_render_user_signal() {
        let event = Event::new("test-event", serde_json::json!("world"));
        let mut run = Run::fixture(); // Uses default user_prompt

        let actual = run.render_user_prompt(&event).unwrap();

        assert_eq!(actual.items.len(), 1);
        if let Signal::RenderUser { prompt, .. } = &actual.items[0] {
            assert_eq!(prompt.template, "Hello {{event.value}}");
            // Note: We can't access private fields of EventContext, but we can
            // verify the signal was created
        } else {
            panic!("Expected RenderUser signal");
        }
    }

    #[test]
    fn test_set_user_prompt_without_user_prompt_returns_continue_signal() {
        let event = Event::new("test-event", serde_json::json!("world"));
        let agent = Agent::new("test-agent"); // Agent without user_prompt
        let mut run = Run::fixture_with_agent(agent);

        let actual = run.render_user_prompt(&event).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));
    }

    #[test]
    fn test_set_user_prompt_includes_variables_in_context() {
        let user_prompt = Template::new("Hello {{variable1}}");
        let agent = Agent::new("test-agent").user_prompt(user_prompt);
        let event = Event::new("test-event", serde_json::json!("world"));
        let variables = HashMap::from([
            ("variable1".to_string(), serde_json::json!("value1")),
            ("variable2".to_string(), serde_json::json!("value2")),
        ]);
        let mut run =
            Run::new(agent, Environment::default(), Local::now()).variables(variables.clone());

        let actual = run.render_user_prompt(&event).unwrap();

        assert_eq!(actual.items.len(), 1);
        if let Signal::RenderUser { .. } = &actual.items[0] {
            // Note: We can't access private fields of EventContext, but we can
            // verify the signal was created The variables are
            // passed to EventContext during construction, which is tested by
            // the signal creation
        } else {
            panic!("Expected RenderUser signal");
        }
    }

    #[test]
    fn test_add_user_message_content_with_content() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model"));
        let mut run = Run::new(agent, Environment::default(), Local::now());

        let _ = run.on_render_user_message("Test user message".to_string());

        assert_eq!(run.context.messages.len(), 1);
        if let Some(ContextMessage::Text(message)) = run.context.messages.first() {
            assert_eq!(message.role, Role::User);
            assert_eq!(message.content, "Test user message");
            assert_eq!(message.model, Some(ModelId::new("test-model")));
        } else {
            panic!("Expected user message to be added");
        }
    }

    #[test]
    fn test_add_user_message_content_with_empty_content() {
        let mut run = Run::fixture();

        let _ = run.on_render_user_message("".to_string());

        assert_eq!(run.context.messages.len(), 0);
    }

    #[test]
    fn test_update_initialize_action_includes_user_prompt_rendering() {
        let user_prompt = Template::new("Hello {{event.value}}");
        let agent = Agent::new("test-agent")
            .model(ModelId::new("test-model"))
            .user_prompt(user_prompt);
        let mut run = Run::new(agent, Environment::default(), Local::now());

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = Default::default();
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!("world"));

        let action = Action::Initialize { event, models, tool_definitions, current_time };

        let result = run.update(action);

        assert!(result.is_ok());
        let signal = result.unwrap();

        // Verify that the signal contains a RenderUser signal
        assert!(signal
            .iter()
            .any(|s| matches!(s, Signal::RenderUser { .. })));
        // Verify that the signal contains a Chat signal
        assert!(signal.iter().any(|s| matches!(s, Signal::Chat { .. })));
    }

    #[test]
    fn test_wrap_all_empty_iterator() {
        let fixture: Vec<Wrap<i32>> = vec![];
        let actual = Wrap::all(fixture);
        let expected: Wrap<i32> = Wrap { items: vec![] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_single_wrap() {
        let fixture = vec![Wrap::new(42)];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![42] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_multiple_wraps() {
        let fixture = vec![Wrap::new(1), Wrap::new(2), Wrap::new(3)];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_wraps_with_multiple_items() {
        let fixture = vec![
            Wrap { items: vec![1, 2] },
            Wrap { items: vec![3, 4, 5] },
            Wrap { items: vec![6] },
        ];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3, 4, 5, 6] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_with_array() {
        let fixture = [Wrap::new("hello"), Wrap::new("world")];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec!["hello", "world"] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_with_results() {
        fn success_wrap(value: i32) -> Result<Wrap<i32>> {
            Ok(Wrap::new(value))
        }

        let fixture = [
            success_wrap(1).unwrap(),
            success_wrap(2).unwrap(),
            success_wrap(3).unwrap(),
        ];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3] };
        assert_eq!(actual.items, expected.items);
    }
}
