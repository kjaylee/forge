use forge_api::ModelId;
use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

use super::Mode;

#[derive(Debug, Default)]
pub struct State {
    #[allow(dead_code)]
    pub model_id: Option<ModelId>,
    pub exit: bool,
    pub suspend: bool,
    pub mode: Mode,
    pub messages: Vec<String>,
}

impl State {
    pub fn key_event(&mut self, key_event: KeyEvent) {
        let (code, modifier) = (key_event.code, key_event.modifiers);

        match (code, modifier) {
            (KeyCode::Char('d'), KeyModifiers::CONTROL) => self.exit = true,
            (KeyCode::Char('c'), KeyModifiers::CONTROL) => self.suspend = true,
            (KeyCode::Char('t'), KeyModifiers::CONTROL) => {
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
