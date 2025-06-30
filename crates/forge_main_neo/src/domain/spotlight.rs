use edtui::{EditorMode, EditorState};

#[derive(Clone)]
pub struct SpotlightState {
    pub is_visible: bool,
    pub editor: EditorState,
}

impl Default for SpotlightState {
    fn default() -> Self {
        let mut editor = EditorState::default();
        editor.mode = EditorMode::Insert;
        Self { is_visible: false, editor }
    }
}
