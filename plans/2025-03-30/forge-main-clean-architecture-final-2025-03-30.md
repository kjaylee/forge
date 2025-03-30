# Forge Main Module Clean Architecture - Final Plan

## Objective

Rewrite the `forge_main` crate using clean architecture principles to achieve:

1. Clear separation of concerns
2. Better testability
3. Reduced coupling between components
4. Improved maintainability and extensibility
5. Comprehensive test coverage

This final plan incorporates refined naming conventions that better reflect domain concepts and align with existing patterns.

## Implementation Plan

### 1. Final Clean Architecture Structure

```
forge_main/
├── Cargo.toml
└── src/
    ├── domain/              
    │   ├── command.rs       # Command domain entities
    │   ├── event.rs         # Event domain entities 
    │   ├── mode.rs          # Mode domain entity
    │   ├── service.rs       # Core service traits
    │   └── state.rs         # Application state
    ├── application/         
    │   ├── app.rs           # Main application logic
    │   ├── ui.rs            # UI abstraction (ports)
    │   └── command.rs       # Command handling
    ├── infrastructure/      
    │   ├── command.rs       # Command service implementation
    │   └── terminal.rs      # Terminal UI implementation
    ├── presentation/        
    │   ├── cli.rs           # CLI components
    │   ├── terminal.rs      # Terminal presentation
    │   └── prompt.rs        # User prompting
    ├── lib.rs               # Library exports
    └── main.rs              # Application entry point
```

### 2. Domain Layer Implementation

```rust
// src/domain/mode.rs
#[derive(Clone, Debug, PartialEq)]
pub struct ForgeMode(String);

impl ForgeMode {
    pub fn new(value: impl ToString) -> Self {
        Self(value.to_string().to_uppercase())
    }
    
    pub fn value(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ForgeMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// src/domain/command.rs
pub enum Command {
    New,
    Message(String),
    Info,
    Exit,
    Models,
    Dump,
    Custom(CommandPayload),
}

pub struct CommandPayload {
    pub name: String,
    pub value: Option<String>,
}

// Command definition struct for registration
pub struct CommandDefinition {
    pub name: String,
    pub description: String,
    pub value: Option<String>,
}

// src/domain/event.rs
pub struct EventBuilder {
    pub name: String,
    pub value: Value,
}

impl EventBuilder {
    pub fn new<V: Into<Value>>(name: impl ToString, value: V) -> Self {
        Self {
            name: name.to_string(),
            value: value.into(),
        }
    }
    
    pub fn into_event(self, mode: Option<&ForgeMode>) -> Event {
        // Create event with mode prefix if available
        let prefix = mode.map(|m| m.to_string().to_lowercase())
            .unwrap_or_else(|| "default".to_string());
            
        let name_parts = vec![prefix, "user".to_string(), self.name];
        Event::new(name_parts, self.value)
    }
}

// src/domain/state.rs
pub struct ForgeState {
    pub current_title: Option<String>,
    pub conversation_id: Option<ConversationId>,
    pub usage: Usage,
    pub mode: Option<ForgeMode>,
    pub is_first: bool,
}

impl Default for ForgeState {
    fn default() -> Self {
        Self {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: None,
            is_first: true,
        }
    }
}

impl ForgeState {
    pub fn get_mode(&self) -> anyhow::Result<&ForgeMode> {
        self.mode.as_ref().ok_or_else(|| anyhow::anyhow!("No mode defined"))
    }
}

// src/domain/service.rs
/// Service interface for command parsing and management
pub trait CommandService: Send + Sync {
    fn parse(&self, input: &str) -> Result<Command>;
    fn register_commands(&self, workflow: &Workflow);
    fn get_command_names(&self) -> Vec<String>;
}

/// Core service trait that provides access to application services
pub trait ForgeServices: Send + Sync + 'static {
    type API: API;
    type CommandService: CommandService;
    
    fn api(&self) -> &Self::API;
    fn command_service(&self) -> &Self::CommandService;
}
```

### 3. Application Layer Implementation

```rust
// src/application/ui.rs
pub trait UserInterface: Send + Sync {
    fn display_message(&self, message: &ChatResponse) -> Result<()>;
    fn display_text(&self, text: &str) -> Result<()>;
    fn display_error(&self, error: &str) -> Result<()>;
    fn display_success(&self, message: &str, details: Option<&str>) -> Result<()>;
    fn prompt_user(&self, prompt: &PromptContext) -> Result<String>;
}

pub struct PromptContext {
    pub title: Option<String>,
    pub usage: Option<Usage>,
    pub mode: Option<ForgeMode>,
}

// src/application/command.rs
pub struct CommandProcessor<S: ForgeServices> {
    services: Arc<S>,
}

impl<S: ForgeServices> CommandProcessor<S> {
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }
    
    pub fn register_workflow_commands(&self, workflow: &Workflow) {
        self.services.command_service().register_commands(workflow);
    }
    
    pub fn parse_command(&self, input: &str) -> Result<Command> {
        self.services.command_service().parse(input)
    }
    
    pub fn get_command_names(&self) -> Vec<String> {
        self.services.command_service().get_command_names()
    }
}

// src/application/app.rs
pub struct ForgeApp<S: ForgeServices, U: UserInterface> {
    services: Arc<S>,
    ui: Arc<U>,
    state: ForgeState,
    command_processor: CommandProcessor<S>,
}

impl<S: ForgeServices, U: UserInterface> ForgeApp<S, U> {
    pub fn new(services: Arc<S>, ui: Arc<U>) -> Self {
        Self {
            command_processor: CommandProcessor::new(services.clone()),
            services,
            ui,
            state: ForgeState::default(),
        }
    }
    
    pub async fn init_conversation(&mut self, workflow_path: Option<&Path>) -> Result<&ConversationId> {
        match &self.state.conversation_id {
            Some(id) => Ok(id),
            None => {
                let workflow = self.services.api().load(workflow_path).await?;
                self.command_processor.register_workflow_commands(&workflow);
                
                let id = self.services.api().init(workflow).await?;
                self.state.conversation_id = Some(id);
                
                // Set initial mode from workflow if available
                if let Some(conversation) = self.services.api().conversation(self.state.conversation_id.as_ref().unwrap()).await? {
                    if let Some(first_mode) = conversation.workflow.modes.first() {
                        let mode = ForgeMode::new(&first_mode.name);
                        self.state.mode = Some(mode.clone());
                        
                        // Set mode variable in conversation
                        self.services.api().set_variable(
                            self.state.conversation_id.as_ref().unwrap(),
                            "mode".to_string(),
                            Value::from(mode.to_string()),
                        ).await?;
                    }
                }
                
                Ok(self.state.conversation_id.as_ref().unwrap())
            }
        }
    }
    
    pub async fn process_user_input(&mut self, content: String) -> Result<()> {
        let conversation_id = self.init_conversation(None).await?;
        
        // Create event with appropriate prefix based on current state
        let is_first = self.state.is_first;
        self.state.is_first = false;
        
        let event_name = if is_first { "task_init" } else { "task_update" };
        let event = EventBuilder::new(event_name, content)
            .into_event(self.state.mode.as_ref());
            
        // Create chat request and process
        let chat = ChatRequest::new(event, conversation_id.clone());
        let mut stream = self.services.api().chat(chat).await?;
        
        self.process_chat_stream(&mut stream).await
    }
    
    pub async fn handle_mode_change(&mut self, mode: ForgeMode) -> Result<()> {
        // Update mode in state
        self.state.mode = Some(mode.clone());
        
        // Set mode in conversation
        let conversation_id = self.init_conversation(None).await?;
        self.services.api()
            .set_variable(
                conversation_id,
                "mode".to_string(),
                Value::from(mode.to_string()),
            )
            .await?;
        
        // Get mode description if available
        let mut description = String::from("custom mode");
        if let Ok(Some(conversation)) = self.services.api().conversation(conversation_id).await {
            if let Some(mode_config) = conversation.workflow.find_mode(&mode.to_string()) {
                description = mode_config.description.clone();
            }
        }
        
        // Display mode change success
        self.ui.display_success(&mode.to_string(), Some(&description))?;
        
        Ok(())
    }
    
    async fn process_chat_stream(
        &mut self,
        stream: &mut impl StreamExt<Item = Result<AgentMessage<ChatResponse>>>
    ) -> Result<()> {
        while let Some(result) = stream.next().await {
            match result {
                Ok(message) => self.handle_chat_response(&message)?,
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
    
    fn handle_chat_response(&mut self, message: &AgentMessage<ChatResponse>) -> Result<()> {
        match &message.message {
            ChatResponse::Text(text) => self.ui.display_text(text)?,
            ChatResponse::Usage(usage) => {
                self.state.usage = usage.clone();
            },
            ChatResponse::Event(event) => {
                if event.name.to_string() == "ui/title" {
                    self.state.current_title = event.value.as_str().map(|s| s.to_string());
                }
            },
            // Handle other response types
            _ => {},
        }
        Ok(())
    }
    
    // Other command handlers (dump, models, info, etc.)
    // ...
}
```

### 4. Infrastructure Layer Implementation

```rust
// src/infrastructure/command.rs
pub struct ForgeCommandService {
    commands: Arc<Mutex<Vec<CommandDefinition>>>,
}

impl Default for ForgeCommandService {
    fn default() -> Self {
        Self {
            commands: Arc::new(Mutex::new(Self::default_commands())),
        }
    }
}

impl ForgeCommandService {
    fn default_commands() -> Vec<CommandDefinition> {
        // Build default commands (new, info, exit, etc.)
        vec![
            CommandDefinition { 
                name: "/new".to_string(), 
                description: "Start a new conversation".to_string(), 
                value: None 
            },
            // Other commands...
        ]
    }
    
    fn extract_command_value(&self, command: &CommandDefinition, parts: &[&str]) -> Option<String> {
        // Implementation similar to current ForgeCommandManager
        // ...
        None
    }
    
    fn find(&self, command_name: &str) -> Option<CommandDefinition> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .find(|c| c.name == command_name)
            .cloned()
    }
}

impl CommandService for ForgeCommandService {
    fn parse(&self, input: &str) -> Result<Command> {
        let trimmed = input.trim();
        if !trimmed.starts_with('/') {
            return Ok(Command::Message(trimmed.to_string()));
        }

        match trimmed {
            "/new" => Ok(Command::New),
            "/info" => Ok(Command::Info),
            "/exit" => Ok(Command::Exit),
            "/models" => Ok(Command::Models),
            "/dump" => Ok(Command::Dump),
            text => {
                let parts = text.split_ascii_whitespace().collect::<Vec<&str>>();
                
                if let Some(command_name) = parts.first() {
                    if let Some(command) = self.find(command_name) {
                        let value = self.extract_command_value(&command, &parts[1..]);
                        
                        // Check if this is a mode command
                        if let Some(mode_name) = command.name.strip_prefix('/') {
                            return Ok(Command::Custom(CommandPayload { 
                                name: "mode".to_string(), 
                                value: Some(mode_name.to_string())
                            }));
                        }
                        
                        // Regular command
                        let name = command.name.strip_prefix('/').unwrap().to_string();
                        Ok(Command::Custom(CommandPayload { 
                            name, 
                            value
                        }))
                    } else {
                        Err(anyhow::anyhow!("{} is not a valid command", command_name))
                    }
                } else {
                    Err(anyhow::anyhow!("Invalid command format"))
                }
            }
        }
    }
    
    fn register_commands(&self, workflow: &Workflow) {
        let mut guard = self.commands.lock().unwrap();
        let mut commands = Self::default_commands();
        
        // Add mode commands from workflow
        for mode in &workflow.modes {
            commands.push(CommandDefinition {
                name: mode.command.clone(),
                description: format!("[MODE] {}", mode.description),
                value: None,
            });
        }
        
        // Add custom commands from workflow
        commands.extend(workflow.commands.clone().into_iter().map(|cmd| {
            CommandDefinition {
                name: format!("/{}", cmd.name),
                description: format!("[COMMAND] {}", cmd.description),
                value: cmd.value.clone(),
            }
        }));
        
        // Sort and replace commands
        commands.sort_by(|a, b| a.name.cmp(&b.name));
        *guard = commands;
    }
    
    fn get_command_names(&self) -> Vec<String> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .map(|cmd| cmd.name.clone())
            .collect()
    }
}

// src/infrastructure/terminal.rs
pub struct TerminalUI {
    // Using existing console output mechanisms
}

impl TerminalUI {
    pub fn new(environment: &Environment) -> Self {
        Self { /* initialize */ }
    }
    
    fn write(&self, text: &str) -> Result<()> {
        // Implementation using existing console tools
        Ok(())
    }
    
    fn writeln(&self, text: &str) -> Result<()> {
        // Implementation using existing console tools
        Ok(())
    }
}

impl UserInterface for TerminalUI {
    fn display_message(&self, message: &ChatResponse) -> Result<()> {
        match message {
            ChatResponse::Text(text) => self.write(&text.dimmed().to_string()),
            // Other message types
            _ => Ok(()),
        }
    }
    
    fn display_text(&self, text: &str) -> Result<()> {
        self.write(text)
    }
    
    fn display_error(&self, error: &str) -> Result<()> {
        self.writeln(&TitleFormat::failed(error).format())
    }
    
    fn display_success(&self, message: &str, details: Option<&str>) -> Result<()> {
        let mut format = TitleFormat::success(message);
        if let Some(details) = details {
            format = format.sub_title(details);
        }
        self.writeln(&format.format())
    }
    
    fn prompt_user(&self, prompt: &PromptContext) -> Result<String> {
        // Implementation using existing prompt tools
        Ok(String::new())
    }
}
```

### 5. Presentation Layer Implementation

```rust
// src/presentation/cli.rs
#[derive(Parser, Debug)]
pub struct Cli {
    #[arg(long)]
    pub restricted: bool,

    #[arg(short, long)]
    pub prompt: Option<String>,

    #[arg(short, long)]
    pub command: Option<PathBuf>,

    #[arg(short, long)]
    pub event: Option<String>,

    #[arg(short, long)]
    pub workflow: Option<String>,

    #[arg(short, long)]
    pub verbose: bool,
}

// src/presentation/prompt.rs
pub struct PromptFormatter {
    title: Option<String>,
    usage: Option<Usage>,
    mode: Option<ForgeMode>,
}

impl Default for PromptFormatter {
    fn default() -> Self {
        Self {
            title: None,
            usage: None,
            mode: None,
        }
    }
}

impl PromptFormatter {
    pub fn title(mut self, title: impl ToString) -> Self {
        self.title = Some(title.to_string());
        self
    }
    
    pub fn usage(mut self, usage: Usage) -> Self {
        self.usage = Some(usage);
        self
    }
    
    pub fn mode(mut self, mode: ForgeMode) -> Self {
        self.mode = Some(mode);
        self
    }
    
    pub fn to_context(&self) -> PromptContext {
        PromptContext {
            title: self.title.clone(),
            usage: self.usage.clone(),
            mode: self.mode.clone(),
        }
    }
}

// src/presentation/terminal.rs
pub struct ForgeTerminal<S: ForgeServices, U: UserInterface> {
    app: ForgeApp<S, U>,
    cli: Cli,
}

impl<S: ForgeServices, U: UserInterface> ForgeTerminal<S, U> {
    pub fn new(services: Arc<S>, ui: Arc<U>, cli: Cli) -> Self {
        Self {
            app: ForgeApp::new(services, ui),
            cli,
        }
    }
    
    pub async fn run(&mut self) -> Result<()> {
        // Handle CLI-specific flows (event dispatch, direct prompt)
        if let Some(dispatch_json) = self.cli.event.clone() {
            let event: EventBuilder = serde_json::from_str(&dispatch_json)?;
            // Handle event dispatch
            return Ok(());
        }

        // Handle direct prompt if provided
        if let Some(prompt) = self.cli.prompt.clone() {
            self.app.process_user_input(prompt).await?;
            return Ok(());
        }

        // Interactive mode with command loop
        // ...
        
        Ok(())
    }
}
```

### 6. Service Implementation and Wiring

```rust
// Implementation of ForgeServices
pub struct StandardForgeServices<A: API> {
    api: Arc<A>,
    command_service: Arc<ForgeCommandService>,
}

impl<A: API> StandardForgeServices<A> {
    pub fn new(api: Arc<A>) -> Self {
        Self {
            api,
            command_service: Arc::new(ForgeCommandService::default()),
        }
    }
}

impl<A: API> ForgeServices for StandardForgeServices<A> {
    type API = A;
    type CommandService = ForgeCommandService;
    
    fn api(&self) -> &Self::API {
        &self.api
    }
    
    fn command_service(&self) -> &Self::CommandService {
        &self.command_service
    }
}

// src/lib.rs
mod application;
mod domain;
mod infrastructure;
mod presentation;

// Public exports
pub use application::app::ForgeApp;
pub use domain::service::{ForgeServices, CommandService};
pub use infrastructure::command::ForgeCommandService;
pub use infrastructure::terminal::TerminalUI;
pub use presentation::cli::Cli;
pub use presentation::terminal::ForgeTerminal;

// Service factory
pub struct ForgeServiceFactory;

impl ForgeServiceFactory {
    pub fn create_services(restricted: bool) -> impl ForgeServices {
        let api = Arc::new(ForgeAPI::init(restricted));
        StandardForgeServices::new(api)
    }
}

// src/main.rs
use clap::Parser;
use forge::{Cli, ForgeServiceFactory, ForgeTerminal, TerminalUI};
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Parse CLI arguments
    let cli = Cli::parse();
    
    // Initialize services
    let services = Arc::new(ForgeServiceFactory::create_services(cli.restricted));
    
    // Create UI
    let ui = Arc::new(TerminalUI::new(&services.api().environment()));
    
    // Create and run console application
    let mut terminal = ForgeTerminal::new(services, ui, cli);
    terminal.run().await
}
```

### 7. Testing Strategy

```rust
// Testable mock implementations
#[cfg(test)]
mod tests {
    use super::*;
    use mockall::predicate::*;
    use mockall::mock;

    // Generate mock for API
    mock! {
        pub MockAPI {}
        #[async_trait]
        impl API for MockAPI {
            // All API methods implemented
        }
    }
    
    // Generate mock for CommandService
    mock! {
        pub MockCommandService {}
        impl CommandService for MockCommandService {
            fn parse(&self, input: &str) -> Result<Command>;
            fn register_commands(&self, workflow: &Workflow);
            fn get_command_names(&self) -> Vec<String>;
        }
    }
    
    // Generate mock for UserInterface
    mock! {
        pub MockUserInterface {}
        impl UserInterface for MockUserInterface {
            fn display_message(&self, message: &ChatResponse) -> Result<()>;
            fn display_text(&self, text: &str) -> Result<()>;
            fn display_error(&self, error: &str) -> Result<()>;
            fn display_success(&self, message: &str, details: Option<&str>) -> Result<()>;
            fn prompt_user(&self, prompt: &PromptContext) -> Result<String>;
        }
    }
    
    // Mock ForgeServices implementation
    pub struct MockForgeServices {
        api: Arc<MockAPI>,
        command_service: Arc<MockCommandService>,
    }
    
    impl ForgeServices for MockForgeServices {
        type API = MockAPI;
        type CommandService = MockCommandService;
        
        fn api(&self) -> &Self::API {
            &self.api
        }
        
        fn command_service(&self) -> &Self::CommandService {
            &self.command_service
        }
    }
    
    // Example test
    #[tokio::test]
    async fn test_process_user_input() {
        // Setup
        let mut mock_api = MockAPI::new();
        let mock_command_service = MockCommandService::new();
        let mock_ui = MockUserInterface::new();
        
        // Configure expectations
        mock_api.expect_load().returning(|_| Ok(Workflow::default()));
        mock_api.expect_init().returning(|_| Ok(ConversationId::new("test-id")));
        mock_api.expect_chat().returning(|_| {
            // Return mock stream
            Ok(/* mock stream implementation */)
        });
        
        // Create services and app
        let services = Arc::new(MockForgeServices {
            api: Arc::new(mock_api),
            command_service: Arc::new(mock_command_service),
        });
        let ui = Arc::new(mock_ui);
        let mut app = ForgeApp::new(services, ui);
        
        // Execute
        let result = app.process_user_input("Test message".to_string()).await;
        
        // Verify
        assert!(result.is_ok());
    }
}
```

## Verification Criteria

1. **Structure Verification**:
   - Clean architecture with proper separation of concerns
   - Uses type parameters instead of trait objects
   - Follows existing codebase patterns with improved naming
   - Minimizes duplication of functionality

2. **Functionality Verification**:
   - All features from the original `forge_main` are preserved
   - Mode switching works as expected
   - Command handling preserves original behavior
   - Event creation includes proper prefixing

3. **Test Coverage Verification**:
   - Each component is testable in isolation
   - Mock implementations enable thorough testing
   - Tests follow the project's standard pattern

4. **Code Quality Verification**:
   - Follows Rust best practices
   - Uses clear, descriptive naming that aligns with domain concepts
   - Properly leverages the type system for safety
   - Clear separation between different layers

This final refined architecture uses improved naming throughout that better reflects domain concepts and responsibilities, emphasizes type parameters over trait objects, aligns with the existing codebase patterns, and provides a clean, testable structure.