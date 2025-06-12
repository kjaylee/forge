use std::sync::Arc;

use anyhow::Context;
use forge_app::TemplateService;
use handlebars::Handlebars;
use rust_embed::Embed;

use crate::{FsReadService, Infrastructure};

#[derive(Embed)]
#[folder = "../../templates/"]
struct Templates;

#[derive(Clone)]
pub struct ForgeTemplateService {
    hb: Arc<Handlebars<'static>>,
}

impl std::fmt::Debug for ForgeTemplateService {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ForgeTemplateService")
            .field("hb", &"<Handlebars>")
            .finish()
    }
}

impl Default for ForgeTemplateService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeTemplateService {
    pub fn new() -> Self {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        // Register all partial templates
        hb.register_embed_templates::<Templates>().unwrap();

        Self { hb: Arc::new(hb) }
    }

    pub async fn try_new<F: Infrastructure>(
        infra: Arc<F>,
        pattern: String,
    ) -> anyhow::Result<Self> {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        // Register all partial templates
        hb.register_embed_templates::<Templates>().unwrap();

        // Load templates from filesystem using glob pattern
        for entry in
            glob::glob(&pattern).with_context(|| format!("Invalid glob pattern: {pattern}"))?
        {
            let path = entry.with_context(|| "Failed to read glob entry")?;
            let template_content = infra.file_read_service().read_utf8(&path).await?;
            // Use the filename (without extension) as the template name
            let template_name = path
                .file_stem()
                .and_then(|name| name.to_str())
                .with_context(|| format!("Invalid filename: {}", path.display()))?;
            hb.register_template_string(template_name, template_content)
                .with_context(|| format!("Failed to register template: {template_name}"))?;
        }

        Ok(Self { hb: Arc::new(hb) })
    }
}

#[async_trait::async_trait]
impl TemplateService for ForgeTemplateService {
    fn render(
        &self,
        template: impl ToString,
        object: &impl serde::Serialize,
    ) -> anyhow::Result<String> {
        let template = template.to_string();
        let rendered = self.hb.render_template(&template, object)?;
        Ok(rendered)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;

    #[test]
    fn test_render_simple_template() {
        // Fixture: Create template service and data
        let service = ForgeTemplateService::new();
        let data = json!({
            "name": "Forge",
            "version": "1.0",
            "features": ["templates", "rendering", "handlebars"]
        });

        // Actual: Render a simple template
        let template = "App: {{name}} v{{version}} - Features: {{#each features}}{{this}}{{#unless @last}}, {{/unless}}{{/each}}";
        let actual = service.render(template, &data).unwrap();

        // Expected: Result should match the expected string
        let expected = "App: Forge v1.0 - Features: templates, rendering, handlebars";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_render_partial_system_info() {
        // Fixture: Create template service and data
        let service = ForgeTemplateService::new();
        let data = json!({
            "env": {
                "os": "test-os",
                "cwd": "/test/path",
                "shell": "/bin/test",
                "home": "/home/test"
            },
            "current_time": "2024-01-01 12:00:00 UTC",
            "files": [
                "/file1.txt",
                "/file2.txt"
            ]
        });

        // Actual: Render the partial-system-info template
        let actual = service
            .render("{{> partial-system-info.hbs }}", &data)
            .unwrap();

        // Expected: Result should contain the rendered system info with substituted
        assert!(actual.contains("<operating_system>test-os</operating_system>"));
    }

    #[test]
    fn test_try_new_with_glob_pattern() {
        use std::fs;

        use tempfile::TempDir;

        // Fixture: Create temporary directory with template files
        let temp_dir = TempDir::new().unwrap();
        let temp_path = temp_dir.path();

        // Create test template files
        let template1_path = temp_path.join("test_template1.md");
        let template2_path = temp_path.join("test_template2.md");
        let template3_path = temp_path.join("other_file.txt");

        fs::write(&template1_path, "Hello {{name}} from template1").unwrap();
        fs::write(&template2_path, "Welcome {{user}} to template2").unwrap();
        fs::write(&template3_path, "This should not be loaded").unwrap();

        let glob_pattern = format!("{}/*.md", temp_path.display());

        // Actual: Create service with glob pattern
        let service = ForgeTemplateService::try_new(glob_pattern).unwrap();
        let data1 = json!({"name": "World"});
        let data2 = json!({"user": "Alice"});

        let actual1 = service.render_template("test_template1", &data1).unwrap();
        let actual2 = service.render_template("test_template2", &data2).unwrap();

        // Expected: Templates should be loaded and rendered correctly
        let expected1 = "Hello World from template1";
        let expected2 = "Welcome Alice to template2";

        assert_eq!(actual1, expected1);
        assert_eq!(actual2, expected2);

        // Verify that non-matching files are not loaded
        assert!(service.render_template("other_file", &json!({})).is_err());
    }

    #[test]
    fn test_try_new_with_invalid_glob_pattern() {
        // Fixture: Invalid glob pattern
        let invalid_pattern = "[invalid-pattern";

        // Actual: Try to create service with invalid pattern
        let actual = ForgeTemplateService::try_new(invalid_pattern.to_string());

        // Expected: Should return an error
        assert!(actual.is_err());
        assert!(actual
            .unwrap_err()
            .to_string()
            .contains("Invalid glob pattern"));
    }
}
