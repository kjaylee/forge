use handlebars::Handlebars;
use serde::Serialize;

use crate::{Error, Platform, Result};

#[derive(Serialize, Debug)]
pub struct EnvironmentValue {
    operating_system: String,
    current_working_dir: String,
    default_shell: String,
    home_directory: String,
}

pub struct Environment;
impl Environment {
    pub fn render(template: &str) -> Result<String> {
        let env = EnvironmentValue {
            operating_system: std::env::consts::OS.to_string(),
            current_working_dir: std::env::current_dir()?.display().to_string(),
            default_shell: if cfg!(windows) {
                std::env::var("COMSPEC").or(Err(Error::IndeterminateShell(Platform::Windows)))?
            } else {
                std::env::var("SHELL").or(Err(Error::IndeterminateShell(Platform::UnixLike)))?
            },
            home_directory: dirs::home_dir()
                .ok_or(Error::IndeterminateHomeDir)?
                .display()
                .to_string(),
        };

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
