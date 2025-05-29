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
    /// Returns whether tools are supported for the agent's model
    ///
    /// This method looks up the agent's model from the models collection
    /// and returns the tool support information:
    /// - Returns None if the agent has no model specified
    /// - Returns None if the model is not found in the models collection
    /// - Returns Some(bool) if the model exists and has tool support
    ///   information
    /// - Returns None if the model exists but has no tool support information
    pub fn tool_supported(&self) -> Option<bool> {
        // Get the model ID from the agent
        let model_id = self.agent.model.as_ref()?;

        // Find the model in the models collection
        let model = self.models.iter().find(|model| &model.id == model_id)?;

        // Return the tool support information
        model.tools_supported
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
    use crate::model::{Model, ModelId};

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

    #[test]
    fn test_run_tool_supported() {
        // Test case 1: Agent has model that exists and supports tools
        let agent = Agent::new("test-agent").model(ModelId::new("gpt-4o"));
        let model = Model::new(ModelId::new("gpt-4o")).tools_supported(true);
        let run = Run::new(agent, vec![model]);
        assert_eq!(run.tool_supported(), Some(true));

        // Test case 2: Agent has model that exists but doesn't support tools
        let agent = Agent::new("test-agent").model(ModelId::new("gpt-3.5-turbo"));
        let model = Model::new(ModelId::new("gpt-3.5-turbo")).tools_supported(false);
        let run = Run::new(agent, vec![model]);
        assert_eq!(run.tool_supported(), Some(false));

        // Test case 3: Agent has model that exists but has null tools_supported
        let agent = Agent::new("test-agent").model(ModelId::new("forge-test-model"));
        let model = Model::new(ModelId::new("forge-test-model"));
        let run = Run::new(agent, vec![model]);
        assert_eq!(run.tool_supported(), None);

        // Test case 4: Agent has model that is not found in the models collection
        let agent = Agent::new("test-agent").model(ModelId::new("nonexistent-model"));
        let model = Model::new(ModelId::new("different-model")).tools_supported(true);
        let run = Run::new(agent, vec![model]);
        assert_eq!(run.tool_supported(), None);

        // Test case 5: Agent has no model specified
        let agent = Agent::new("test-agent"); // No model set
        let model = Model::new(ModelId::new("some-model")).tools_supported(true);
        let run = Run::new(agent, vec![model]);
        assert_eq!(run.tool_supported(), None);

        // Test case 6: Multiple models in collection, correct one is found
        let agent = Agent::new("test-agent").model(ModelId::new("model-2"));
        let models = vec![
            Model::new(ModelId::new("model-1")).tools_supported(false),
            Model::new(ModelId::new("model-2")).tools_supported(true),
            Model::new(ModelId::new("model-3")).tools_supported(false),
        ];
        let run = Run::new(agent, models);
        assert_eq!(run.tool_supported(), Some(true));
    }
}
