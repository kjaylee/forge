use derive_more::From;
use ratatui::crossterm::event::Event;

use crate::domain::command::Command;

/// Top-level application actions that wrap route-specific actions
#[derive(Clone, From, Debug, PartialEq)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse {
        message: String,
    },
    Tagged(TaggedAction),
}

#[derive(Clone, From, Debug, PartialEq)]
pub struct TaggedAction(Box<Action>, &'static str);

impl TaggedAction {
    pub fn update(&self, id: &'static str, f: impl FnOnce(Action) -> Command) -> Command {
        if self.1 == id {
            f(self.0.as_ref().clone()).tag(id)
        } else {
            Command::Empty
        }
    }
}

impl Action {
    pub fn tag(self, name: &'static str) -> Self {
        Action::Tagged(TaggedAction(Box::new(self), name))
    }
}
