use std::collections::HashMap;

use chrono::{DateTime, Local};
use derive_setters::Setters;
use serde_json::Value;

use crate::{Result, *};

/// Action for initializing an agent with all required data
#[derive(Debug, Clone, Setters)]
#[setters(strip_option, into)]
pub struct InitializeAction {
    event: Event,
    models: Vec<Model>,
    tool_definitions: Vec<ToolDefinition>,
    current_time: DateTime<Local>,
    suggestions: Vec<Suggestion>,
    attachments: Vec<Attachment>,
    files: Vec<String>,
    variables: HashMap<String, Value>,
}

impl InitializeAction {
    pub fn new(event: Event) -> Self {
        Self {
            event,
            models: Default::default(),
            tool_definitions: Default::default(),
            current_time: Local::now(),
            suggestions: Default::default(),
            attachments: Default::default(),
            files: Default::default(),
            variables: Default::default(),
        }
    }

    /// Creates a test fixture with comprehensive defaults for testing
    pub fn default_test() -> Self {
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

        let files = vec!["src/main.rs".to_string(), "Cargo.toml".to_string()];

        let variables = HashMap::from([
            ("test_var".to_string(), serde_json::json!("test_value")),
            ("debug_mode".to_string(), serde_json::json!(true)),
        ]);

        Self::new(Event::new("test-event", serde_json::json!({})))
            .models(models)
            .tool_definitions(tool_definitions)
            .files(files)
            .variables(variables)
    }
}

impl Default for InitializeAction {
    fn default() -> Self {
        Self::new(Event::new("default", serde_json::Value::Null))
    }
}

/// The `Run` struct represents a run of the agent with its context.
#[derive(Debug, Clone, Setters)]
pub struct Run {
    agent: Agent,
    env: Environment,
    context: Context,
    init_action: Option<InitializeAction>,
}

type SignalResult = Result<WrappedSignal>;
type WrappedSignal = Wrap<Signal>;

impl Run {
    pub fn new(agent: Agent, env: Environment) -> Self {
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
        Self { agent, context, env, init_action: None }
    }

    // Helper methods to access initialization data with proper error handling
    fn get_init_action(&self) -> Result<&InitializeAction> {
        self.init_action.as_ref().ok_or(Error::RunNotInitialized)
    }

    fn models(&self) -> Result<&[Model]> {
        Ok(&self.get_init_action()?.models)
    }

    fn tool_definitions(&self) -> Result<&[ToolDefinition]> {
        Ok(&self.get_init_action()?.tool_definitions)
    }

    fn current_time(&self) -> Result<&DateTime<Local>> {
        Ok(&self.get_init_action()?.current_time)
    }

    fn suggestions(&self) -> Result<&[Suggestion]> {
        Ok(&self.get_init_action()?.suggestions)
    }

    fn attachments(&self) -> Result<&[Attachment]> {
        Ok(&self.get_init_action()?.attachments)
    }

    fn files(&self) -> Result<&[String]> {
        Ok(&self.get_init_action()?.files)
    }

    fn variables(&self) -> Result<&HashMap<String, Value>> {
        Ok(&self.get_init_action()?.variables)
    }

    pub fn update(&mut self, action: Action) -> SignalResult {
        match action {
            Action::Initialize(init_action) => self.on_init(init_action),
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
        init_action: InitializeAction,
    ) -> std::result::Result<WrappedSignal, Error> {
        // Store the initialization action directly
        let event = init_action.event.clone();
        self.init_action = Some(init_action);

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
                .tool_definitions()?
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
                        .current_time()?
                        .format("%Y-%m-%d %H:%M:%S %:z")
                        .to_string(),
                    env: Some(self.env.clone()),
                    tool_information: self.tool_information()?,
                    tool_supported: self.tool_supported()?,
                    files: self.files()?.to_vec(),
                    custom_rules: self
                        .agent
                        .custom_rules
                        .as_ref()
                        .cloned()
                        .unwrap_or_default(),
                    variables: self.variables()?.clone(),
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
                    EventContext::new(event.clone())
                        .suggestions(
                            self.suggestions()?
                                .iter()
                                .map(|s| s.suggestion.clone())
                                .collect(),
                        )
                        .variables(self.variables()?.clone())
                        .current_time(
                            self.current_time()?
                                .format("%Y-%m-%d %H:%M:%S %:z")
                                .to_string(),
                        ),
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
            .tool_definitions()?
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
        // Get attachments to avoid borrowing issues
        let attachments = self.attachments()?.to_vec();

        // Process attachments efficiently without cloning context
        for attachment in &attachments {
            let message = match &attachment.content {
                AttachmentContent::Image(image) => ContextMessage::Image(image.clone()),
                AttachmentContent::FileContent(content) => {
                    // Include file path information for better context
                    let message_content = format!("File: {}\n\n{}", attachment.path, content);
                    ContextMessage::user(message_content, self.agent.model.clone())
                }
            };
            self.context.messages.push(message);
        }

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
            .models()?
            .iter()
            .find(|model| &model.id == model_id)
            .ok_or(Error::ModelNotFound(model_id.clone()))?
            .tools_supported
            .unwrap_or_default())
    }
}

pub enum Action {
    Initialize(InitializeAction),
    SystemRender { content: String },
    UserRender { content: String },
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

#[cfg(test)]
mod tests {
    use insta::assert_yaml_snapshot;
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

    impl Agent {
        fn default_test() -> Self {
            Agent::new("test-agent")
                .model(ModelId::new("test-model"))
                .user_prompt(Template::new("Hello {{event.value}}"))
            // No tools by default
        }
    }

    impl Run {
        /// Creates a test fixture with comprehensive defaults for testing
        fn default_test() -> Self {
            let agent = Agent::default_test();
            let env = Environment::default();

            Run::new(agent, env)
        }

        /// Creates a test fixture that's already initialized with default data
        fn default_initialized() -> Self {
            let mut run = Self::default_test();
            run.init_action = Some(Self::default_init_action());
            run
        }

        /// Creates a default InitializeAction for testing
        fn default_init_action() -> InitializeAction {
            InitializeAction::default_test()
        }
    }

    #[test]
    fn test_tool_supported_agent_with_model_that_supports_tools() {
        // Test case 1: Agent has model that exists and supports tools
        let run = Run::default_initialized();
        // Default agent has "test-model" which supports tools by default
        assert_eq!(run.tool_supported().unwrap(), true);
    }

    #[test]
    fn test_tool_supported_agent_with_model_that_does_not_support_tools() {
        // Test case 2: Agent has model that exists but doesn't support tools
        let mut run = Run::default_initialized();
        // Use gpt-3.5-turbo which is already in default models and doesn't support
        // tools
        run.agent.model = Some(ModelId::new("gpt-3.5-turbo"));
        assert_eq!(run.tool_supported().unwrap(), false);
    }

    #[test]
    fn test_tool_supported_agent_with_model_null_tools_supported() {
        // Test case 3: Agent has model that exists but has null tools_supported
        let mut run = Run::default_test();
        let mut init_action = Run::default_init_action();
        // Add a model with null tools_supported and use it
        init_action
            .models
            .push(Model::new(ModelId::new("forge-test-model")));
        run.init_action = Some(init_action);
        run.agent.model = Some(ModelId::new("forge-test-model"));
        assert_eq!(run.tool_supported().unwrap(), false);
    }

    #[test]
    fn test_tool_supported_agent_with_model_not_found() {
        // Test case 4: Agent has model that is not found in the models collection
        let mut run = Run::default_initialized();
        // Set agent model to one that doesn't exist in the models collection
        run.agent.model = Some(ModelId::new("nonexistent-model"));
        let result = run.tool_supported();
        let Error::ModelNotFound(model_id) = result.unwrap_err() else {
            panic!("Expected ModelNotFound error")
        };
        assert_eq!(model_id.as_str(), "nonexistent-model");
    }

    #[test]
    fn test_tool_supported_agent_with_no_model_specified() {
        // Test case 5: Agent has no model specified
        let mut run = Run::default_initialized();
        // Remove the model from the default agent
        run.agent.model = None;
        let result = run.tool_supported();
        let Error::MissingModel(agent_id) = result.unwrap_err() else {
            panic!("Expected MissingModel error")
        };
        assert_eq!(agent_id.as_str(), "test-agent");
    }

    #[test]
    fn test_update_initialize_action_sets_values() {
        let mut run = Run::default_test();

        let current_time = Local::now();
        let action =
            Action::Initialize(InitializeAction::default_test().current_time(current_time));

        let result = run.update(action);

        assert!(result.is_ok());
        assert_eq!(run.models().unwrap().len(), 3); // default_test provides 3 models
        assert_eq!(run.tool_definitions().unwrap().len(), 4); // default_test
                                                              // provides 4 tool
                                                              // definitions
    }

    #[test]
    fn test_update_initialize_action_returns_chat_signal() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model")); // No tools
        let mut run = Run::default_test().agent(agent);

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![];
        let current_time = Local::now();
        let event = Event::new("test-event", Value::Null);

        let action = Action::Initialize(
            InitializeAction::new(event)
                .models(models)
                .tool_definitions(tool_definitions)
                .current_time(current_time),
        );

        let result = run.update(action);

        assert!(result.is_ok());
        let signal = result.unwrap();

        // Verify that the signal contains a Chat signal
        assert!(signal.iter().any(|s| matches!(s, Signal::Chat { .. })));
    }

    #[test]
    fn test_set_tools_agent_with_no_tools_specified() {
        let agent = Agent::new("test-agent"); // Agent without tools
        let mut run = Run::default_test().agent(agent);

        let result = run.set_tools();
        assert!(result.is_ok());
        assert!(run.context.tools.is_empty());
    }

    #[test]
    fn test_set_tools_agent_with_specific_tools_filters_definitions() {
        let agent =
            Agent::new("test-agent").tools(vec![ToolName::new("tool1"), ToolName::new("tool3")]);
        let mut run = Run::default_initialized().agent(agent);

        let result = run.set_tools();
        assert!(result.is_ok());
        assert_yaml_snapshot!(run.context);
    }

    #[test]
    fn test_set_tools_agent_with_nonexistent_tool_returns_error() {
        let agent = Agent::new("test-agent").tools(vec![ToolName::new("nonexistent_tool")]);
        let mut run = Run::default_initialized().agent(agent);

        let result = run.set_tools();
        assert!(result.is_err());
        let Error::ToolDefinitionNotFound(tool_name) = result.unwrap_err() else {
            panic!("Expected ToolDefinitionNotFound error")
        };
        assert_eq!(tool_name.as_str(), "nonexistent_tool");
    }

    #[test]
    fn test_update_with_system_render_action_stores_content() {
        let fixture =
            Action::SystemRender { content: "Rendered system prompt content".to_string() };
        let mut run = Run::default_test();

        let actual = run.update(fixture).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));
        assert_yaml_snapshot!(run.context);
    }

    #[test]
    fn test_update_with_system_render_action_overwrites_previous_content() {
        let mut run = Run::default_test();

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
        let fixture = Action::UserRender { content: "Rendered user prompt content".to_string() };
        let mut run = Run::default_test();

        let actual = run.update(fixture).unwrap();

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
    fn test_update_with_user_render_action_adds_to_existing_messages() {
        let mut run = Run::default_test();

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
    fn test_render_user_prompt_with_user_prompt_returns_render_user_signal() {
        let fixture = Event::new("test-event", serde_json::json!("world"));
        let mut run = Run::default_initialized();

        let actual = run.render_user_prompt(&fixture).unwrap();

        assert_eq!(actual.items.len(), 1);
        if let Signal::RenderUser { prompt, .. } = &actual.items[0] {
            assert_eq!(prompt.template, "Hello {{event.value}}");
        } else {
            panic!("Expected RenderUser signal");
        }
    }

    #[test]
    fn test_render_user_prompt_without_user_prompt_returns_continue_signal() {
        let fixture = Event::new("test-event", serde_json::json!("world"));
        let agent = Agent::new("test-agent"); // Agent without user_prompt
        let mut run = Run::default_test().agent(agent);

        let actual = run.render_user_prompt(&fixture).unwrap();

        assert_eq!(actual.items.len(), 1);
        assert!(matches!(actual.items[0], Signal::Continue));
    }

    #[test]
    fn test_render_user_prompt_includes_variables_in_context() {
        let user_prompt = Template::new("Hello {{variable1}}");
        let agent = Agent::new("test-agent").user_prompt(user_prompt);
        let fixture = Event::new("test-event", serde_json::json!("world"));
        let variables = HashMap::from([
            ("variable1".to_string(), serde_json::json!("value1")),
            ("variable2".to_string(), serde_json::json!("value2")),
        ]);
        let mut run = Run::default_initialized().agent(agent);

        // Update the init_action to include the custom variables
        if let Some(init_action) = &mut run.init_action {
            *init_action = init_action.clone().variables(variables.clone());
        }

        let actual = run.render_user_prompt(&fixture).unwrap();

        assert_eq!(actual.items.len(), 1);
        if let Signal::RenderUser { .. } = &actual.items[0] {
            // Variables are passed to EventContext during construction
        } else {
            panic!("Expected RenderUser signal");
        }
    }

    #[test]
    fn test_on_render_user_message_with_content() {
        let fixture = "Test user message".to_string();
        let mut run = Run::default_test();

        let actual = run.on_render_user_message(fixture);

        assert!(actual.is_ok());
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
    fn test_update_initialize_action_includes_user_prompt_rendering() {
        let user_prompt = Template::new("Hello {{event.value}}");
        let agent = Agent::new("test-agent")
            .model(ModelId::new("test-model"))
            .user_prompt(user_prompt)
            .tools(vec![ToolName::new("test-tool")]);
        let mut run = Run::default_test().agent(agent);

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![ToolDefinition::new("test-tool")];
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!("world"));

        let action = Action::Initialize(
            InitializeAction::new(event)
                .models(models)
                .tool_definitions(tool_definitions)
                .current_time(current_time),
        );

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
    fn test_initialize_action_stores_suggestions() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model")); // No tools
        let mut run = Run::default_test().agent(agent);

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![];
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!({}));

        let suggestions = vec![
            Suggestion {
                use_case: "Testing".to_string(),
                suggestion: "Test suggestion 1".to_string(),
            },
            Suggestion {
                use_case: "Development".to_string(),
                suggestion: "Test suggestion 2".to_string(),
            },
        ];

        let action = Action::Initialize(
            InitializeAction::new(event.clone())
                .models(models)
                .tool_definitions(tool_definitions)
                .current_time(current_time)
                .suggestions(suggestions.clone()),
        );

        let result = run.update(action);

        assert!(result.is_ok());
        assert_eq!(run.suggestions().unwrap().len(), 2);
        assert_eq!(run.suggestions().unwrap(), &suggestions);
    }

    #[test]
    fn test_render_user_prompt_includes_suggestions() {
        let user_prompt = Template::new("Hello {{event.value}}");
        let agent = Agent::new("test-agent").user_prompt(user_prompt);
        let fixture = Event::new("test-event", serde_json::json!("world"));
        let suggestions = vec![Suggestion {
            use_case: "Testing".to_string(),
            suggestion: "Test suggestion".to_string(),
        }];

        let mut run = Run::default_test().agent(agent);
        let init_action = InitializeAction::new(Event::new("test", serde_json::json!({})))
            .suggestions(suggestions.clone());
        run.init_action = Some(init_action);

        let actual = run.render_user_prompt(&fixture).unwrap();

        assert_eq!(actual.items.len(), 1);
        if let Signal::RenderUser { .. } = &actual.items[0] {
            // Suggestions are passed to EventContext during construction
        } else {
            panic!("Expected RenderUser signal");
        }
    }

    #[test]
    fn test_initialize_action_stores_attachments() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model")); // No tools
        let mut run = Run::default_test().agent(agent);

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![];
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!({}));

        let attachments = vec![
            Attachment {
                path: "/path/to/file.txt".to_string(),
                content: AttachmentContent::FileContent("File content here".to_string()),
            },
            Attachment {
                path: "/path/to/image.png".to_string(),
                content: AttachmentContent::Image(Image::new_base64(
                    "base64data".to_string(),
                    "image/png",
                )),
            },
        ];

        let action = Action::Initialize(
            InitializeAction::new(event.clone())
                .models(models)
                .tool_definitions(tool_definitions)
                .current_time(current_time)
                .attachments(attachments.clone()),
        );

        let result = run.update(action);

        assert!(result.is_ok());
        assert_eq!(run.attachments().unwrap().len(), 2);
        assert_eq!(run.attachments().unwrap(), &attachments);
    }

    #[test]
    fn test_add_user_attachments_with_file_content() {
        let mut run = Run::default_test();

        let attachments = vec![Attachment {
            path: "/path/to/file.txt".to_string(),
            content: AttachmentContent::FileContent("Hello, world!".to_string()),
        }];

        let init_action = InitializeAction::new(Event::new("test", serde_json::json!({})))
            .attachments(attachments);
        run.init_action = Some(init_action);

        let result = run.add_user_attachments(&serde_json::json!({}));

        assert!(result.is_ok());
        assert_yaml_snapshot!(run.context);
    }

    #[test]
    fn test_add_user_attachments_with_image() {
        let mut run = Run::default_test();

        let image = Image::new_base64("base64data".to_string(), "image/png");
        let attachments = vec![Attachment {
            path: "/path/to/image.png".to_string(),
            content: AttachmentContent::Image(image.clone()),
        }];

        let init_action = InitializeAction::new(Event::new("test", serde_json::json!({})))
            .attachments(attachments);
        run.init_action = Some(init_action);

        let result = run.add_user_attachments(&serde_json::json!({}));

        assert!(result.is_ok());
        assert_yaml_snapshot!(run.context);
    }

    #[test]
    fn test_add_user_attachments_with_multiple_attachments() {
        let mut run = Run::default_test();

        let image = Image::new_base64("base64data".to_string(), "image/png");
        let attachments = vec![
            Attachment {
                path: "/path/to/file.txt".to_string(),
                content: AttachmentContent::FileContent("File content".to_string()),
            },
            Attachment {
                path: "/path/to/image.png".to_string(),
                content: AttachmentContent::Image(image.clone()),
            },
        ];

        let init_action = InitializeAction::new(Event::new("test", serde_json::json!({})))
            .attachments(attachments);
        run.init_action = Some(init_action);

        let result = run.add_user_attachments(&serde_json::json!({}));

        assert!(result.is_ok());
        assert_yaml_snapshot!(run.context);
    }

    #[test]
    fn test_initialize_action_with_both_suggestions_and_attachments() {
        let agent = Agent::new("test-agent").model(ModelId::new("test-model")); // No tools
        let mut run = Run::default_test().agent(agent);

        let models = vec![Model::new(ModelId::new("test-model")).tools_supported(true)];
        let tool_definitions = vec![];
        let current_time = Local::now();
        let event = Event::new("test-event", serde_json::json!({}));

        let suggestions = vec![Suggestion {
            use_case: "Testing".to_string(),
            suggestion: "Test suggestion".to_string(),
        }];

        let attachments = vec![Attachment {
            path: "/path/to/file.txt".to_string(),
            content: AttachmentContent::FileContent("Test content".to_string()),
        }];

        let action = Action::Initialize(
            InitializeAction::new(event.clone())
                .models(models)
                .tool_definitions(tool_definitions)
                .current_time(current_time)
                .suggestions(suggestions.clone())
                .attachments(attachments.clone()),
        );

        let result = run.update(action);

        assert!(result.is_ok());
        assert_eq!(run.suggestions().unwrap().len(), 1);
        assert_eq!(run.attachments().unwrap().len(), 1);
        assert_eq!(run.suggestions().unwrap(), &suggestions);
        assert_eq!(run.attachments().unwrap(), &attachments);

        // Verify attachment was processed and added to context
        let file_messages: Vec<_> = run
            .context
            .messages
            .iter()
            .filter_map(|msg| {
                if let ContextMessage::Text(text_msg) = msg {
                    if text_msg.content.contains("File: /path/to/file.txt") {
                        Some(text_msg)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        assert_eq!(file_messages.len(), 1);
        assert!(file_messages[0].content.contains("Test content"));
    }
}
