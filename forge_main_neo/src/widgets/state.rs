use forge_api::ModelId;
use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

#[derive(Debug, Default)]
pub struct State {
    pub model_id: Option<ModelId>,
    pub exit: bool,
    pub suspend: bool,
    pub mode: Mode,
}

#[derive(Debug, Clone)]
pub struct Mode(String);

impl Default for Mode {
    fn default() -> Self {
        Self("ACT".to_string())
    }
}

impl AsRef<str> for Mode {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl Mode {
    pub fn new<T: AsRef<str>>(value: T) -> Self {
        Self(value.as_ref().to_string())
    }
}

impl State {
    pub fn handle_key_event(&mut self, key_event: KeyEvent) {
        let (code, modifier) = (key_event.code, key_event.modifiers);

        match (code, modifier) {
            (KeyCode::Char('d'), KeyModifiers::CONTROL) => self.exit = true,
            (KeyCode::Char('c'), KeyModifiers::CONTROL) => self.suspend = true,
            (KeyCode::Char('m'), KeyModifiers::ALT) => {
                if self.mode.as_ref() == "PLAN" {
                    self.mode = Mode::new("ACT");
                } else {
                    self.mode = Mode::new("PLAN");
                }
            }
            _ => {}
        }
    }
}
