use std::sync::Arc;

use anyhow::Context;
use forge_app::TemplateService;
use futures::future;
use handlebars::Handlebars;
use rust_embed::Embed;
use tokio::sync::RwLock;

use crate::{FsReadService, Infrastructure};

#[derive(Embed)]
#[folder = "../../templates/"]
struct Templates;

#[derive(Clone)]
pub struct ForgeTemplateService<F> {
    hb: Arc<RwLock<Handlebars<'static>>>,
    infra: Arc<F>,
}

impl<F: Infrastructure> ForgeTemplateService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        // Register all partial templates
        hb.register_embed_templates::<Templates>().unwrap();

        Self { hb: Arc::new(RwLock::new(hb)), infra }
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> TemplateService for ForgeTemplateService<F> {
    async fn register_template(&self, path: String) -> anyhow::Result<()> {
        // Always treat the input as a glob pattern
        let template_paths: Vec<std::path::PathBuf> = glob::glob(&path)
            .with_context(|| format!("Invalid glob pattern: {path}"))?
            .collect::<Result<Vec<_>, _>>()
            .with_context(|| "Failed to read glob entries")?
            .into_iter()
            .filter(|p| p.is_file()) // Only include files, not directories
            .collect();

        // Read all template files in parallel
        let file_read_futures: Vec<_> = template_paths
            .iter()
            .map(|template_path| async move {
                let content = self
                    .infra
                    .file_read_service()
                    .read_utf8(template_path)
                    .await?;

                let template_name = template_path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .with_context(|| format!("Invalid filename: {}", template_path.display()))?;

                anyhow::Ok((template_name.to_string(), content))
            })
            .collect();

        // Await all futures to read template contents
        let results = future::join_all(file_read_futures)
            .await
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?;

        // Register all templates
        let mut guard = self.hb.write().await;
        for (template_name, template_content) in results {
            guard
                .register_template_string(&template_name, template_content)
                .with_context(|| format!("Failed to register template: {template_name}"))?;
        }
        Ok(())
    }

    async fn render(
        &self,
        template: impl ToString + Send,
        object: &(impl serde::Serialize + Sync),
    ) -> anyhow::Result<String> {
        let template = template.to_string();
        let rendered = self.hb.read().await.render_template(&template, object)?;
        Ok(rendered)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    #[tokio::test]
    async fn test_render_simple_template() {
        // Fixture: Create template service and data
        let service = ForgeTemplateService::new(Arc::new(MockInfrastructure::new()));
        let data = json!({
            "name": "Forge",
            "version": "1.0",
            "features": ["templates", "rendering", "handlebars"]
        });

        // Actual: Render a simple template
        let template = "App: {{name}} v{{version}} - Features: {{#each features}}{{this}}{{#unless @last}}, {{/unless}}{{/each}}";
        let actual = service.render(template, &data).await.unwrap();

        // Expected: Result should match the expected string
        let expected = "App: Forge v1.0 - Features: templates, rendering, handlebars";
        assert_eq!(actual, expected);
    }

    #[tokio::test]
    async fn test_render_partial_system_info() {
        // Fixture: Create template service and data
        let service = ForgeTemplateService::new(Arc::new(MockInfrastructure::new()));
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
            .render("{{> forge-partial-system-info.hbs }}", &data)
            .await
            .unwrap();

        // Expected: Result should contain the rendered system info with substituted
        assert!(actual.contains("<operating_system>test-os</operating_system>"));
    }
}
