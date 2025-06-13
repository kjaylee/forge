use handlebars::Handlebars;
use rust_embed::Embed;

#[derive(Embed)]
#[folder = "../../templates/"]
pub struct Templates;

impl Templates {
    /// Render templates without service dependency
    pub fn render(template: &str, object: &impl serde::Serialize) -> anyhow::Result<String> {
        // Create handlebars instance with same configuration as ForgeTemplateService
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        // Register all partial templates
        hb.register_embed_templates::<Templates>()?;

        // Render the template
        let rendered = hb.render_template(template, object)?;
        Ok(rendered)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;

    #[test]
    fn test_render_template_simple() {
        // Fixture: Create test data
        let data = json!({
            "name": "Forge",
            "version": "1.0",
            "features": ["templates", "rendering", "handlebars"]
        });

        // Actual: Render a simple template
        let template = "App: {{name}} v{{version}} - Features: {{#each features}}{{this}}{{#unless @last}}, {{/unless}}{{/each}}";
        let actual = Templates::render(template, &data).unwrap();

        // Expected: Result should match the expected string
        let expected = "App: Forge v1.0 - Features: templates, rendering, handlebars";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_template_with_partial() {
        // Fixture: Create test data
        let data = json!({
            "env": {
                "os": "test-os",
                "cwd": "/test/path",
                "shell": "/bin/test",
                "home": "/home/test"
            },
            "files": [
                "/file1.txt",
                "/file2.txt"
            ],
            "current_time": "2024-01-01 12:00:00 +00:00"
        });

        // Actual: Render the partial-system-info template
        let actual = Templates::render("{{> forge-partial-system-info.hbs }}", &data).unwrap();

        // Expected: Result should contain the rendered system info with substituted
        // values
        assert!(actual.contains("<operating_system>test-os</operating_system>"));
    }

    #[test]
    fn test_render_template_summary_frame() {
        use pretty_assertions::assert_eq;

        // Fixture: Create test data for the summary frame template
        let data = serde_json::json!({
            "summary": "This is a test summary of the conversation"
        });

        // Actual: Render the partial-summary-frame template
        let actual = Templates::render("{{> forge-partial-summary-frame.hbs}}", &data).unwrap();

        // Expected: Result should contain the framed summary text
        let expected = "Use the following summary as the authoritative reference for all coding\nsuggestions and decisions. Do not re-explain or revisit it unless I ask.\n\n<summary>\nThis is a test summary of the conversation\n</summary>\n\nProceed with implementation based on this context.";
        assert_eq!(actual.trim(), expected);
    }
}
