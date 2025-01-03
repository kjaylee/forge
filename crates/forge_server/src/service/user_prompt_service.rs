use crate::Result;
use forge_env::Environment;
use handlebars::Handlebars;

#[async_trait::async_trait]
pub trait UserPromptService: Send + Sync {
    async fn get_user_prompt(&self, task: impl ToString) -> Result<String>;
}

struct Live {
    env: Environment,
}

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

        let ctx = Context {
            env: self.env.clone(),
            task: task.to_string(),
        };

        Ok(hb.render_template(template.as_str(), &ctx)?)
    }
}
