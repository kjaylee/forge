use anyhow::Result;
use forge_api::{ConversationId, Usage};

use super::mode::ForgeMode;

pub struct ForgeState {
    pub current_title: Option<String>,
    pub conversation_id: Option<ConversationId>,
    pub usage: Usage,
    pub mode: Option<ForgeMode>,
    pub is_first: bool,
}

impl Default for ForgeState {
    fn default() -> Self {
        Self {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: None,
            is_first: true,
        }
    }
}

impl ForgeState {
    pub fn get_mode(&self) -> Result<&ForgeMode> {
        self.mode.as_ref().ok_or_else(|| {
            anyhow::anyhow!(
                "No mode defined. At least one mode must be configured in the workflow."
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_get_mode_with_mode() {
        // Create ForgeState with a mode
        let fixture = ForgeState {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: Some(ForgeMode::new("ACT")),
            is_first: true,
        };

        // Test get_mode returns the mode
        let actual = fixture.get_mode().expect("Mode should be present");
        assert_eq!(actual, "ACT");
    }

    #[test]
    fn test_get_mode_without_mode() {
        // Create ForgeState without a mode
        let fixture = ForgeState {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: None,
            is_first: true,
        };

        // Test get_mode returns an error
        let result = fixture.get_mode();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("No mode defined"));
    }
}
