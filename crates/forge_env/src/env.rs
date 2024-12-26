use handlebars::Handlebars;
use serde::Serialize;

use crate::Result;

#[derive(Serialize)]
pub struct EnvironmentValue {
    operating_system: String,
    current_working_dir: String,
}

impl EnvironmentValue {
    pub fn build() -> Self {
        EnvironmentValue {
            operating_system: std::env::consts::OS.to_string(),
            current_working_dir: format!("{}", std::env::current_dir().unwrap().display()),
        }
    }
}

pub struct Environment;
impl Environment {
    pub fn render<C: Serialize>(template: &str, context: &C) -> Result<String> {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        Ok(hb.render_template(template, context)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_with_custom_context() {
        let context = EnvironmentValue {
            operating_system: "test-os".into(),
            current_working_dir: "test-dir".into(),
        };
        let result = Environment::render(
            "OS: {{operating_system}}, CWD: {{current_working_dir}}",
            &context,
        )
        .unwrap();
        assert_eq!(result, "OS: test-os, CWD: test-dir");
    }
}
