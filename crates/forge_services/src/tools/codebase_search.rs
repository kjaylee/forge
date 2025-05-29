use std::sync::Arc;

use forge_display::TitleFormat;
use forge_domain::CodebaseSearchInput;
use forge_domain::EnvironmentService;
use forge_domain::ExecutableTool;
use forge_domain::NamedTool;
use forge_domain::ToolCallContext;
use forge_domain::ToolDescription;
use forge_domain::ToolOutput;
use forge_tool_macros::ToolDescription;

use crate::FsReadService;
use crate::IndexerService;
use crate::Infrastructure;

/// Find snippets of code from the codebase most relevant to the search query.
/// This is a semantic search tool, so the query should ask for something semantically matching what is needed.
/// If it makes sense to only search in particular directories, please specify them in the target_directories field.
/// Unless there is a clear reason to use your own search query, please just reuse the user's exact query with their wording.
/// Their exact wording/phrasing can often be helpful for the semantic search query. Keeping the same exact question format can also be helpful.
#[derive(ToolDescription)]
pub struct CodebaseSearch<F>(Arc<F>);

impl<F: Infrastructure> CodebaseSearch<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self(infra)
    }
}

impl<F: Infrastructure> NamedTool for CodebaseSearch<F> {
    fn tool_name() -> forge_domain::ToolName {
        forge_domain::ToolName::new("forge_tool_codebase_search")
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
struct Location {
    column: usize,
    line: usize,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct Offset {
    start: usize,
    end: usize,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct Span {
    start: Location,
    end: Location,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct QueryOutput {
    path: String,
    kind: String,
    span: Span,
    scope: Option<String>,
    offset: Offset,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for CodebaseSearch<F> {
    type Input = CodebaseSearchInput;

    async fn call(
        &self,
        context: ToolCallContext,
        input: Self::Input,
    ) -> anyhow::Result<ToolOutput> {
        context
            .send_text(TitleFormat::debug(format!(
                "Codebase Search for {}",
                input.query
            )))
            .await?;

        let results = self
            .0
            .indexer_service()
            .query::<QueryOutput>(&input.query)
            .await?;

        let mut code_snippets = String::new();

        let cwd = self.0.environment_service().get_environment().cwd;

        for result in results {
            let file_path = cwd.join(&result.path);
            let code = match self.0.file_read_service().read_utf8(&file_path).await {
                Ok(file_content) => {
                    let content = &file_content[result.offset.start..=result.offset.end];
                    content.to_string()
                }
                Err(_e) => continue,
            };

            code_snippets.push_str(
                format!(
                    "<code_block path=\"{}\" char_start=\"{}\" char_end=\"{}\">\n",
                    result.path, result.offset.start, result.offset.end
                )
                .as_str(),
            );
            code_snippets.push_str(&code);
            code_snippets.push_str("\n</code_block>");
            code_snippets.push('\n');
        }

        Ok(ToolOutput::text(code_snippets))
    }
}
