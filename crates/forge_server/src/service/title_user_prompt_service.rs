use handlebars::Handlebars;
use serde::Serialize;

use super::user_prompt_service::UserPromptService;
use super::Service;
use crate::Result;

impl Service {
    pub fn title_user_prompt_service() -> impl UserPromptService {
        Live {}
    }
}

struct Live;

#[derive(Serialize)]
struct Context {
    task: String,
}

#[async_trait::async_trait]
impl UserPromptService for Live {
    async fn get_user_prompt(&self, task: &str) -> Result<String> {
        let template = include_str!("../prompts/title/user_task.md");

        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        let ctx = Context { task: task.to_string() };

        Ok(hb.render_template(template, &ctx)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_rendered_prompt() {
        let user_prompt = Service::title_user_prompt_service()
            .get_user_prompt("write fibo seq in rust")
            .await
            .unwrap();
        insta::assert_snapshot!(user_prompt);
    }
}
