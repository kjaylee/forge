use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use forge_api::{API, Agent, ChatRequest, Event, Workflow};
use futures::StreamExt;
use futures::future::join_all;
use serde::Serialize;

use super::{PullRequest, Rule, SummaryAgent};
use crate::infra::{Config, ProjectRules, ReviewInfrastructure, TemplateRender};

pub struct ArchitectureAgent<I> {
    pull_request: Arc<PullRequest>,
    file: PathBuf,
    infra: Arc<I>,
}

#[derive(Serialize)]
struct PromptContext<'a> {
    file: &'a PathBuf,
    pull_request: &'a PullRequest,
    rule: &'a Rule,
}

impl<I: ReviewInfrastructure> ArchitectureAgent<I> {
    pub fn new(review: Arc<PullRequest>, file: PathBuf, infra: Arc<I>) -> Self {
        Self { pull_request: review, file, infra }
    }

    async fn create_prompt(&self, template: &str, rule: &Rule) -> Result<String> {
        let context = PromptContext { file: &self.file, rule, pull_request: &self.pull_request };
        self.infra.template_renderer().render(&template, context)
    }

    async fn _summarize(&self) -> Result<String> {
        let rules = self.infra.project_rules().rules().await?.rules;
        let template = &self.infra.config().get("architect.prompt").await?;

        let failures = join_all(rules.iter().map(|rule| async move {
            let cause = self.check_rule(&template, rule).await?;
            Ok((rule, cause))
        }))
        .await
        .into_iter()
        .collect::<Result<Vec<_>>>()?;

        let failures = failures
            .into_iter()
            .filter_map(|(rule, cause)| cause.map(|cause| (rule.content.clone(), cause)))
            .collect::<Vec<_>>();

        if failures.is_empty() {
            Ok("No architecture issues found".to_string())
        } else {
            Ok(failures
                .into_iter()
                .fold(String::new(), |acc, (rule, cause)| {
                    format!(r#"{acc}\n<rule ="{rule}">{cause}</rule>"#)
                }))
        }
    }

    async fn check_rule(&self, template: &str, rule: &Rule) -> Result<Option<String>> {
        let agent = Agent::new("architect").subscribe(vec!["user".to_string()]);
        let workflow = Workflow::default().agents(vec![agent]);
        let conversation = self.infra.forge_workflow().init(workflow).await?;
        let prompt = self.create_prompt(template, rule).await?;
        let event = Event::new("user", prompt);
        let chat = ChatRequest::new(event, conversation);
        let mut stream = self.infra.forge_workflow().chat(chat).await?;

        while let Some(response) = stream.next().await {
            let response = response?;
            match response.message {
                forge_api::ChatResponse::Event(event) if event.name == "failure" => {
                    return Ok(Some(event.value));
                }
                _ => {}
            }
        }
        Ok(None)
    }
}

#[async_trait::async_trait]
impl<I: ReviewInfrastructure> SummaryAgent for ArchitectureAgent<I> {
    async fn summarize(&self) -> anyhow::Result<String> {
        self._summarize().await
    }
}
