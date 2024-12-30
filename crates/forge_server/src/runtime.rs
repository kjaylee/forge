use std::sync::{Arc, RwLock};

use forge_provider::{Request, ResultStream};
use futures::future::join_all;
use serde::Serialize;
use tokio::sync::Mutex;
use tokio_stream::StreamExt;

use crate::Storage;

pub trait ConversationContext: Clone + Send + Sync {
    fn id(&self) -> String;
}

impl ConversationContext for Arc<RwLock<Request>> {
    fn id(&self) -> String {
        self.read()
            .unwrap()
            .conversation_id
            .clone()
            .expect("at the point conversation_id should be set")
    }
}

pub trait Application: Send + Sync + Sized + Clone {
    type Action: Send;
    type Error: Send;
    type Command: Send;
    type Context: ConversationContext + Send;
    fn run(
        self,
        context: Self::Context,
        action: impl Into<Self::Action>,
    ) -> std::result::Result<(Self, Vec<Self::Command>), Self::Error>;

    #[allow(unused)]
    fn run_seq(
        self,
        context: Self::Context,
        actions: Vec<Self::Action>,
    ) -> Result<(Self, Vec<Self::Command>), Self::Error>
    where
        Self::Action: Clone,
        Self::Context: Clone,
    {
        let mut this = self;
        let mut commands = Vec::new();
        for action in actions {
            let (s, c) = this.run(context.clone(), action.clone())?;
            this = s;
            commands.extend(c)
        }

        Ok((this, commands))
    }
}

#[derive(Clone)]
pub struct ApplicationRuntime<A: Application, S: Storage> {
    state: Arc<Mutex<A>>,
    storage: Arc<S>,
}

impl<A: Application, S: Storage> ApplicationRuntime<A, S> {
    pub fn new(app: A, storage: Arc<S>) -> Self {
        Self { state: Arc::new(Mutex::new(app)), storage }
    }
}

impl<A: Application + 'static, S: Storage + 'static> ApplicationRuntime<A, S> {
    #[async_recursion::async_recursion]
    pub async fn execute<'a>(
        &'a self,
        context: A::Context,
        action: A::Action,
        executor: Arc<
            impl Executor<Command = A::Command, Action = A::Action, Error = A::Error> + 'static,
        >,
    ) -> std::result::Result<(), A::Error>
    where
        A::Context: Clone + Serialize,
    {
        let mut guard = self.state.lock().await;
        let app = guard.clone();
        let (app, commands) = app.run(context.clone(), action)?;
        *guard = app;
        drop(guard);

        // on every succesfull action, save the context.
        let conversation_id = context.id();
        let _ = self.storage.save(&conversation_id, &context).await;

        join_all(commands.into_iter().map(|command| {
            let executor = executor.clone();
            let context = context.clone();
            async move {
                let _: Result<(), A::Error> = async move {
                    let mut stream = executor.clone().execute(&command).await?;
                    while let Some(action) = stream.next().await {
                        let this = self.clone();
                        let executor = executor.clone();
                        // NOTE: The `execute` call needs to run sequentially. Executing it
                        // asynchronously would disrupt the order of `toolUse` content, leading to
                        // mixed-up.
                        this.execute(context.clone(), action?, executor).await?;
                    }

                    Ok(())
                }
                .await;
            }
        }))
        .await;

        Ok(())
    }
}

#[async_trait::async_trait]
pub trait Executor: Send + Sync {
    type Command;
    type Action;
    type Error;
    async fn execute(&self, command: &Self::Command) -> ResultStream<Self::Action, Self::Error>;
}
