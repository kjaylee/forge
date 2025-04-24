
use forge_api::{ModeDefinitions, Workflow};
use forge_domain::{
    Agent, AgentId, EventContext, ModeConfig, ModelId, SystemContext, Template, ToolName,
};

/// System prompt for the developer agent
const SYSTEM_PROMPT: &str = r#"
Use the tools at your disposal and solve the user given task.

First, let's establish the current system information:

{{> partial-system-info.hbs}}

"#;

/// User prompt for the developer agent
const USER_PROMPT: &str = r#"<task>{{event.value}}</task>

Hints:
- There is a .md file that contains the name of the cat.
"#;

/// Creates a test workflow that mimics the configuration from
/// test_workflow.yaml
pub fn create_test_workflow() -> Workflow {
    // Create the developer agent
    let developer = Agent::new(AgentId::new("developer"))
        .model(ModelId::new("anthropic/claude-3.5-sonnet"))
        .tool_supported(true)
        .tools(vec![
            ToolName::new("tool_forge_fs_read"),
            ToolName::new("tool_forge_fs_search"),
        ])
        .subscribe(vec!["user_task_init".to_string()])
        .ephemeral(false)
        .user_prompt(Template::<EventContext>::new(USER_PROMPT.trim()));

    // Add mode-specific system prompt
    let mut modes = ModeDefinitions::new();

    modes.insert(
        "act".into(),
        ModeConfig::new().system_prompt(Template::<SystemContext>::new(SYSTEM_PROMPT.trim())),
    );

    // Set the modes on the developer agent
    let developer = developer.modes(modes);

    // Using the new Workflow::new() function instead of default()
    Workflow::new().agents(vec![developer])
}
