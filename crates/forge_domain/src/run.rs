use chrono::{DateTime, Local};
use serde_json::Value;

use crate::*;

/// The `Run` struct represents a run of the agent with its context.
pub struct Run {
    pub agent: Agent,
    pub context: Context,
    pub current_time: DateTime<Local>,
    pub models: Vec<Model>,
}

type SignalResult = anyhow::Result<Signal>;

impl Run {
    pub fn new(agent: Agent, models: Vec<Model>) -> Self {
        let mut context = Context::default();
        if let Some(top_k) = agent.top_k {
            context = context.top_k(top_k);
        }
        if let Some(temperature) = agent.temperature {
            context = context.temperature(temperature);
        }
        if let Some(top_p) = agent.top_p {
            context = context.top_p(top_p);
        }
        Self { agent, models, context, current_time: Local::now() }
    }

    pub fn update(&mut self, event: Action) -> SignalResult {
        match event {
            Action::Initialize(event) => {
                self.set_system_prompt()?;
                self.set_tools()?;
                self.add_user_message(&event.value)?;
                self.add_user_attachments(&event.value)?;
                Ok(Signal::default())
            }
            Action::Message(message) => {
                self.collect_message(message?)?;
                Ok(Signal::default())
            }
        }
    }

    fn set_system_prompt(&mut self) -> SignalResult {
        todo!()
    }

    fn set_tools(&mut self) -> SignalResult {
        todo!()
    }

    fn add_user_message(&mut self, _message: &Value) -> SignalResult {
        todo!()
    }

    fn add_user_attachments(&mut self, _message: &Value) -> SignalResult {
        todo!()
    }

    fn collect_message(&mut self, _message: ChatCompletionMessage) -> SignalResult {
        todo!()
    }
}

pub enum Action {
    Initialize(Event),
    Message(anyhow::Result<ChatCompletionMessage>),
}

#[derive(Default)]
pub enum Signal {
    #[default]
    Continue,
    Stop,
    Chat {
        agent: Box<Agent>,
        context: Context,
    },
}

#[cfg(test)]
mod tests {

    use pretty_assertions::assert_eq;

    use super::*;
    use crate::agent::Agent;

    #[test]
    fn test_run_new() {
        let agent = Agent::new("my-agent").temperature(0.5).top_k(10).top_p(0.9);
        let run = Run::new(agent, vec![]);
        assert_eq!(run.agent.id.as_str(), "my-agent");
        assert!(run.context.messages.is_empty());
        assert!(run.models.is_empty());
        assert_eq!(run.context.top_k.map(|x| x.value()), Some(10));
        assert_eq!(run.context.temperature.map(|x| x.value()), Some(0.5));
        assert_eq!(run.context.top_p.map(|x| x.value()), Some(0.9));
    }
}
