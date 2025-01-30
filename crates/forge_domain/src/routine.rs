use crate::{Agent, ChatCompletionMessage, Context, ModelId, ResultStream};

#[async_trait::async_trait]
pub trait ChatProvider: Send + Sync + 'static {
    async fn chat(
        &self,
        model_id: &ModelId,
        request: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error>;
}

pub trait ForgeDomain: Send + Sync + 'static {
    type ChatProvider: ChatProvider;
    fn chat_provider(&self) -> &Self::ChatProvider;
}

pub struct Routine<'a, S, U, D: ForgeDomain> {
    system: S,
    user: U,
    domain: &'a D,
}

impl<'a, S, U, D: ForgeDomain> Routine<'a, S, U, D> {
    pub fn new(domain: &'a D, system: S, user: U) -> Self {
        Self { system, user, domain }
    }

    pub fn launch(&self, agent: Agent<S, U>) -> anyhow::Result<()> {
        todo!()
    }
}
