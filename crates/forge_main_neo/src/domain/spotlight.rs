use edtui::EditorState;

#[derive(Default, Clone)]
pub struct SpotlightState {
    pub is_visible: bool,
    pub editor: EditorState
}
