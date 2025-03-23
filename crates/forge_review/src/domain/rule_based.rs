use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use forge_api::{API, Agent, ChatRequest, Event, Workflow};
use futures::StreamExt;
use futures::future::join_all;
use serde::Serialize;

use super::{PullRequest, Rule, SummaryAgent};
use crate::infra::{Config, ProjectRules, ReviewInfrastructure, TemplateRender};

pub struct RuleAgent<I, R> {
    pull_request: Arc<PullRequest>,
    file: PathBuf,
    rule_repo: Arc<R>,
    infra: Arc<I>,
    prompt_key: String,
    agent_name: String,
}

#[derive(Serialize)]
struct PromptContext<'a> {
    file: &'a PathBuf,
    pull_request: &'a PullRequest,
    rule: &'a Rule,
}

impl<I: ReviewInfrastructure, R: ProjectRules> RuleAgent<I, R> {
    pub fn new(
        name: impl Into<String>,
        prompt_key: impl Into<String>,
        review: Arc<PullRequest>,
        file: PathBuf,
        infra: Arc<I>,
        rules: Arc<R>,
    ) -> Self {
        Self {
            agent_name: name.into(),
            prompt_key: prompt_key.into(),
            pull_request: review,
            file,
            infra,
            rule_repo: rules,
        }
    }

    async fn create_prompt(&self, template: &str, rule: &Rule) -> Result<String> {
        let context = PromptContext { file: &self.file, rule, pull_request: &self.pull_request };
        self.infra.template_renderer().render(template, context)
    }

    async fn _summarize(&self) -> Result<String> {
        let rules = self.rule_repo.rules().await?.rules;
        let template = &self.infra.config().get(&self.prompt_key).await?;

        let failures = join_all(rules.iter().map(|rule| async move {
            let cause = self.check_rule(template, rule).await?;
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
            Ok("No issues found".to_string())
        } else {
            Ok(failures
                .into_iter()
                .fold(String::new(), |acc, (rule, cause)| {
                    format!(r#"{acc}\n<rule ="{rule}">{cause}</rule>"#)
                }))
        }
    }

    async fn check_rule(&self, template: &str, rule: &Rule) -> Result<Option<String>> {
        let agent = Agent::new(self.agent_name.clone()).subscribe(vec!["user".to_string()]);
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
impl<I: ReviewInfrastructure, R: ProjectRules> SummaryAgent for RuleAgent<I, R> {
    async fn summarize(&self) -> anyhow::Result<String> {
        self._summarize().await
    }
}
