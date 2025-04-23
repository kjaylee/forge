use std::sync::Arc;

use chrono::Local;
use forge_domain::{
    Agent, Compact, Context, EnvironmentService, Event, EventContext, Mode, SystemContext,
    Template, TemplateService, ToolService,
};
use forge_walker::Walker;
use handlebars::Handlebars;
use rust_embed::Embed;
use tracing::debug;

use crate::Infrastructure;

// Include README.md at compile time
const README_CONTENT: &str = include_str!("../../../README.md");

#[derive(Embed)]
#[folder = "../../templates/"]
struct Templates;

#[derive(Clone)]
pub struct ForgeTemplateService<F, T> {
    hb: Handlebars<'static>,
    infra: Arc<F>,
    tool_service: Arc<T>,
}

impl<F, T> ForgeTemplateService<F, T> {
    pub fn new(infra: Arc<F>, tool_service: Arc<T>) -> Self {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        // Register all partial templates
        hb.register_embed_templates::<Templates>().unwrap();

        Self { hb, infra, tool_service }
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure, T: ToolService> TemplateService for ForgeTemplateService<F, T> {
    async fn render_system(
        &self,
        agent: &Agent,
        prompt: &Template<SystemContext>,

        mode: Mode,
    ) -> anyhow::Result<String> {
        let env = self.infra.environment_service().get_environment();

        // Build the walker, only setting max_depth if a value was provided
        let mut walker = Walker::max_all();

        // Only set max_depth if the value is provided
        // Create maximum depth for file walker, defaulting to 1 if not specified
        walker = walker.max_depth(agent.max_walker_depth.unwrap_or(1));

        let mut files = walker
            .cwd(env.cwd.clone())
            .get()
            .await?
            .iter()
            .map(|f| f.path.to_string())
            .collect::<Vec<_>>();

        // Sort the files alphabetically to ensure consistent ordering
        files.sort();

        // Get current date and time with timezone
        let current_time = Local::now().format("%Y-%m-%d %H:%M:%S %:z").to_string();

        // Use the mode passed directly to the method

        // Filter tool information based on the mode
        let tool_information = if agent.tool_supported.unwrap_or_default() {
            Some(self.tool_service.usage_prompt_for_mode(agent, mode.clone()))
        } else {
            None
        };

        // Create the context with README content for all agents
        let ctx = SystemContext {
            current_time,
            env: Some(env),
            tool_information,
            tool_supported: agent.tool_supported.unwrap_or_default(),
            files,
            readme: README_CONTENT.to_string(),
            custom_rules: agent.custom_rules.as_ref().cloned().unwrap_or_default(),
            mode,
        };

        // Render the template with the context
        let result = self.hb.render_template(prompt.template.as_str(), &ctx)?;
        Ok(result)
    }

    async fn render_event(
        &self,
        _agent: &Agent,
        prompt: &Template<EventContext>,
        event: &Event,
    ) -> anyhow::Result<String> {
        // Create an EventContext with the provided event
        let event_context = EventContext::new(event.clone());

        // Variables removed

        debug!(event_context = ?event_context, "Event context");

        // Render the template with the event context
        Ok(self
            .hb
            .render_template(prompt.template.as_str(), &event_context)?)
    }

    async fn render_summarization(
        &self,
        compaction: &Compact,
        context: &Context,
    ) -> anyhow::Result<String> {
        let summary_tag = compaction.summary_tag.as_ref().cloned().unwrap_or_default();
        let ctx = serde_json::json!({
            "context": context.to_text(),
            "summary_tag": summary_tag
        });

        // Render the template with the context
        let result = self.hb.render_template(
            compaction
                .prompt
                .as_deref()
                .unwrap_or("{{> system-prompt-context-summarizer.hbs}}"),
            &ctx,
        )?;
        Ok(result)
    }
}
