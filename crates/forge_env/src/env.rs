use handlebars::Handlebars;
use serde::Serialize;

use crate::Result;

#[derive(Serialize, Debug)]
pub struct EnvironmentValue {
    operating_system: String,
    current_working_directory: String,
}

impl EnvironmentValue {
    pub fn build() -> Self {
        EnvironmentValue {
            operating_system: std::env::consts::OS.to_string(),
            current_working_directory: format!("{}", std::env::current_dir().unwrap().display()),
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

pub mod tests {
    use super::*;

    // use crate::default_ctx for unit test in the project.
    pub fn default_ctx() -> EnvironmentValue {
        EnvironmentValue {
            current_working_directory: "/Users/test".into(),
            operating_system: "TestOS".into(),
        }
    }

    #[test]
    fn test_render_with_custom_context() {
        let result = Environment::render(
            "OS: {{operating_system}}, CWD: {{current_working_directory}}",
            &default_ctx(),
        )
        .unwrap();
        assert_eq!(result, "OS: TestOS, CWD: /Users/test");
    }
}
