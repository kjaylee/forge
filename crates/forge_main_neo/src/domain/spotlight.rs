use edtui::{EditorMode, EditorState};

#[derive(Clone)]
pub struct SpotlightState {
    pub is_visible: bool,
    pub editor: EditorState,
    pub selected_index: usize,
    pub commands: Vec<(String, String)>,
}

impl Default for SpotlightState {
    fn default() -> Self {
        let mut editor = EditorState::default();
        editor.mode = EditorMode::Insert;
        let commands = vec![
            ("exit".to_string(), "Exit the application".to_string()),
            (
                "workspace".to_string(),
                "Read and analyze the current workspace".to_string(),
            ),
            (
                "chat".to_string(),
                "Send a message to the AI assistant".to_string(),
            ),
            (
                "clear".to_string(),
                "Clear a running timer interval".to_string(),
            ),
            (
                "model".to_string(),
                "Select an AI model for the spotlight".to_string(),
            ),
            (
                "agent".to_string(),
                "Select an AI agent for the spotlight".to_string(),
            ),
        ];
        Self { is_visible: false, editor, selected_index: 0, commands }
    }
}
