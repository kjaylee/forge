use handlebars::Handlebars;
use serde::Serialize;

// Partials
const TOOL_USE_PROMPT: &str = include_str!("./tool_use.md");

pub struct Prompt {
    template: String,
}

impl Prompt {
    pub fn new(template: impl ToString) -> Self {
        Self { template: template.to_string() }
    }

    pub fn render(&self, data: &impl Serialize) -> anyhow::Result<String> {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());
        hb.register_partial("tool_use", TOOL_USE_PROMPT)?;

        Ok(hb.render_template(&self.template, data)?)
    }
}
