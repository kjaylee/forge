//! Default configuration for Forge
//!
//! This module contains the default configuration that is used when no
//! custom configuration is provided.

use std::collections::HashMap;

use forge_domain::{
    Agent, AgentId, EventContext, ModelId, SystemContext, Template, ToolName, Workflow,
};
use serde_json::json;

/// The original default forge.yaml content as a string constant.
/// Kept for reference and backwards compatibility.
pub const DEFAULT_FORGE_YAML: &str = r#"# YAML Variables
advanced_model: &advanced_model anthropic/claude-3.7-sonnet
efficiency_model: &efficiency_model anthropic/claude-3.5-haiku

variables:
  mode: ACT
agents:
  - id: title_generation_worker
    model: *efficiency_model
    tool_supported: true
    tools:
      - tool_forge_event_dispatch
    subscribe:
      - user_task_init
    system_prompt: "{{> system-prompt-title-generator.hbs }}"
    user_prompt: <technical_content>{{event.value}}</technical_content>

  - id: help_agent
    model: google/gemini-2.0-flash-thinking-exp:free
    tools:
      - tool_forge_fs_read
      - tool_forge_fs_create
    subscribe:
      - user_help_query
    system_prompt: |
      {{> system-prompt-help.hbs }}
    user_prompt: <query>{{event.value}}</query>

  - id: software-engineer
    model: *advanced_model
    tool_supported: true
    tools:
      - tool_forge_fs_read
      - tool_forge_fs_create
      - tool_forge_fs_remove
      - tool_forge_fs_patch
      - tool_forge_process_shell
      - tool_forge_net_fetch
      - tool_forge_fs_search
    subscribe:
      - user_task_init
      - user_task_update
    ephemeral: false
    max_walker_depth: 4
    system_prompt: "{{> system-prompt-engineer.hbs }}"
    user_prompt: |
      <task>{{event.value}}</task>
      <mode>{{variables.mode}}</mode>

  - id: github-task-agent
    model: *advanced_model
    tool_supported: true
    tools:
      - tool_forge_fs_read
      - tool_forge_fs_create
      - tool_forge_fs_remove
      - tool_forge_fs_patch
      - tool_forge_process_shell
      - tool_forge_net_fetch
      - tool_forge_fs_search
      - tool_forge_event_dispatch
    subscribe:
      - fix_issue
      - update_pr
    ephemeral: false
    max_walker_depth: 4
    system_prompt: |
      {{> system-prompt-engineer.hbs }}

      ## GitHub Task Management

      ### Workflow Steps

      **For `fix_issue` events:**
      1. First, retrieve the issue details using `gh issue view {issue_number}`
      2. Create a new branch named `forge-{issue_number}`
      3. Create a `.task-{issue_number}.md` file containing:
         - Original issue details (title, description)
         - A plan to fix the issue
         - Requirements and acceptance criteria
      4. Create a draft PR with the initial commit containing only the task file
      5. Push this initial commit and record the PR number for future reference

      **For `update_pr` events:**
      1. Check out the branch associated with the PR using `gh pr checkout {pr_number}`
      2. Read the `.task-{issue_number}.md` file to understand the task
      3. Check for any PR comments using `gh pr view {pr_number} --comments` and incorporate feedback
      4. Implement the required changes in small, focused commits
      5. Push commits frequently to show progress
      6. Update the task file with your progress after each significant step
      7. When the task is fully completed, mark the PR as ready for review with `gh pr ready {pr_number}`

      ### Guidelines
      - Always create the task file first before making code changes
      - Make small, incremental commits with descriptive messages
      - Comment on the PR with progress updates after significant changes
      - Ensure all tests pass before marking the PR as ready
      - Use proper Git practices (check branch status, pull before push)
      - Always push changes to remote to make them visible
      - When stuck, describe the issue in the PR comments
    user_prompt: |
      <event>{{event.name}}</event>
      <value>{{event.value}}</value>
      <mode>ACT</mode>
"#;

/// System prompt templates for each agent type
mod prompts {
    /// Title generation agent system prompt template
    pub const TITLE_GENERATOR: &str = "{{> system-prompt-title-generator.hbs }}";

    /// Help agent system prompt template
    pub const HELP: &str = "{{> system-prompt-help.hbs }}";

    /// Software engineer agent system prompt template
    pub const ENGINEER: &str = "{{> system-prompt-engineer.hbs }}";

    /// GitHub engineer agent system prompt template - extends the regular
    /// engineer
    pub const GITHUB_ENGINEER: &str = "{{> system-prompt-engineer.hbs }}\n\n## GitHub Task Management\n\n### Workflow Steps\n\n**For `fix_issue` events:**\n1. First, retrieve the issue details using `gh issue view {issue_number}`\n2. Create a new branch named `forge-{issue_number}`\n3. Create a `.task-{issue_number}.md` file containing:\n   - Original issue details (title, description)\n   - A plan to fix the issue\n   - Requirements and acceptance criteria\n4. Create a draft PR with the initial commit containing only the task file\n5. Push this initial commit and record the PR number for future reference\n\n**For `update_pr` events:**\n1. Check out the branch associated with the PR using `gh pr checkout {pr_number}`\n2. Read the `.task-{issue_number}.md` file to understand the task\n3. Check for any PR comments using `gh pr view {pr_number} --comments` and incorporate feedback\n4. Implement the required changes in small, focused commits\n5. Push commits frequently to show progress\n6. Update the task file with your progress after each significant step\n7. When the task is fully completed, mark the PR as ready for review with `gh pr ready {pr_number}`\n\n### Guidelines\n- Always create the task file first before making code changes\n- Make small, incremental commits with descriptive messages\n- Comment on the PR with progress updates after significant changes\n- Ensure all tests pass before marking the PR as ready\n- Use proper Git practices (check branch status, pull before push)\n- Always push changes to remote to make them visible\n- When stuck, describe the issue in the PR comments";
}

/// Creates the default workflow using Rust constructors and setters
pub fn create_default_workflow() -> Workflow {
    // Define model IDs for reuse
    let advanced_model = ModelId::new("anthropic/claude-3.7-sonnet");
    let efficiency_model = ModelId::new("anthropic/claude-3.5-haiku");

    // Create the title generation worker agent
    let title_generation_worker = Agent::new(AgentId::new("title_generation_worker"))
        .model(efficiency_model.clone())
        .tool_supported(true)
        .tools(vec![ToolName::new("tool_forge_event_dispatch")])
        .subscribe(vec!["user_task_init".to_string()])
        .system_prompt(Template::<SystemContext>::new(prompts::TITLE_GENERATOR))
        .user_prompt(Template::<EventContext>::new(
            "<technical_content>{{event.value}}</technical_content>",
        ));

    // Create the help agent
    let help_agent = Agent::new(AgentId::new("help_agent"))
        .model(ModelId::new("google/gemini-2.0-flash-thinking-exp:free"))
        .tools(vec![
            ToolName::new("tool_forge_fs_read"),
            ToolName::new("tool_forge_fs_create"),
        ])
        .subscribe(vec!["user_help_query".to_string()])
        .system_prompt(Template::<SystemContext>::new(prompts::HELP))
        .user_prompt(Template::<EventContext>::new(
            "<query>{{event.value}}</query>",
        ));

    // Create the software engineer agent
    let software_engineer = Agent::new(AgentId::new("software-engineer"))
        .model(advanced_model.clone())
        .tool_supported(true)
        .tools(vec![
            ToolName::new("tool_forge_fs_read"),
            ToolName::new("tool_forge_fs_create"),
            ToolName::new("tool_forge_fs_remove"),
            ToolName::new("tool_forge_fs_patch"),
            ToolName::new("tool_forge_process_shell"),
            ToolName::new("tool_forge_net_fetch"),
            ToolName::new("tool_forge_fs_search"),
        ])
        .subscribe(vec![
            "user_task_init".to_string(),
            "user_task_update".to_string(),
        ])
        .ephemeral(false)
        .max_walker_depth(4_usize)
        .system_prompt(Template::<SystemContext>::new(prompts::ENGINEER))
        .user_prompt(Template::<EventContext>::new(
            "<task>{{event.value}}</task>\n<mode>{{variables.mode}}</mode>",
        ));

    // Create variables map
    let mut variables = HashMap::new();
    variables.insert("mode".to_string(), json!("ACT"));

    // Create the GitHub task agent
    let github_task_agent = Agent::new(AgentId::new("github-task-agent"))
        .model(advanced_model.clone())
        .tool_supported(true)
        .tools(vec![
            ToolName::new("tool_forge_fs_read"),
            ToolName::new("tool_forge_fs_create"),
            ToolName::new("tool_forge_fs_remove"),
            ToolName::new("tool_forge_fs_patch"),
            ToolName::new("tool_forge_process_shell"),
            ToolName::new("tool_forge_net_fetch"),
            ToolName::new("tool_forge_fs_search"),
            ToolName::new("tool_forge_event_dispatch"),
        ])
        .subscribe(vec!["fix_issue".to_string(), "update_pr".to_string()])
        .ephemeral(false)
        .max_walker_depth(4_usize)
        .system_prompt(Template::<SystemContext>::new(prompts::GITHUB_ENGINEER))
        .user_prompt(Template::<EventContext>::new(
            "<event>{{event.name}}</event>\n<value>{{event.value}}</value>\n<mode>ACT</mode>",
        ));

    // Create the workflow with all agents
    Workflow::default()
        .agents(vec![
            title_generation_worker,
            help_agent,
            software_engineer,
            github_task_agent,
        ])
        .variables(variables)
}
