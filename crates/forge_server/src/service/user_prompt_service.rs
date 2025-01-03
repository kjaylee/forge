use forge_env::Environment;
use handlebars::Handlebars;
use serde::Serialize;

use super::Service;
use crate::Result;

#[async_trait::async_trait]
pub trait UserPromptService: Send + Sync {
    async fn get_user_prompt(&self, task: &str) -> Result<String>;
}

impl Service {
    pub fn user_prompt_service(env: Environment) -> impl UserPromptService {
        Live { env }
    }
}

struct Live {
    env: Environment,
}

#[derive(Serialize)]
struct Context {
    env: Environment,
    task: String,
}

#[async_trait::async_trait]
impl UserPromptService for Live {
    async fn get_user_prompt(&self, task: &str) -> Result<String> {
        let template = include_str!("../prompts/user_task.md").to_string();

        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        let ctx = Context { env: self.env.clone(), task: task.to_string() };

        Ok(hb.render_template(template.as_str(), &ctx)?)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub struct TestUserPrompt;

    #[async_trait::async_trait]
    impl UserPromptService for TestUserPrompt {
        async fn get_user_prompt(&self, task: &str) -> Result<String> {
            Ok(format!("<task>{}</task>", task))
        }
    }
}
