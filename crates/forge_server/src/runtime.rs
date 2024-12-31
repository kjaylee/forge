use std::sync::Arc;

use forge_provider::ResultStream;
use futures::future::join_all;
use serde::Serialize;
use tokio::sync::Mutex;
use tokio_stream::StreamExt;

use crate::Storage;

pub trait Application: Send + Sync + Sized + Clone {
    type Action: Send + Sync;
    type Error: Send;
    type Command: Send;
    fn run(
        self,
        action: impl Into<Self::Action>,
    ) -> std::result::Result<(Self, Vec<Self::Command>), Self::Error>;

    #[allow(unused)]
    fn run_seq(self, actions: Vec<Self::Action>) -> Result<(Self, Vec<Self::Command>), Self::Error>
    where
        Self::Action: Clone,
    {
        let mut this = self;
        let mut commands = Vec::new();
        for action in actions {
            let (s, c) = this.run(action.clone())?;
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

#[derive(Serialize)]
struct ExecutionState<A: Serialize, B: Serialize> {
    app: A,
    action: B,
}

impl<A: Application + 'static + Serialize, S: Storage + 'static> ApplicationRuntime<A, S> {
    #[async_recursion::async_recursion]
    pub async fn execute<'a>(
        &'a self,
        action: A::Action,
        executor: Arc<
            impl Executor<Command = A::Command, Action = A::Action, Error = A::Error> + 'static,
        >,
    ) -> std::result::Result<(), A::Error>
    where
        A::Action: Serialize + Clone,
    {
        let mut guard = self.state.lock().await;
        let app = guard.clone();

        // before calling app.run -> persist the current app(line no 84) and action. -> replace the app with the new app in db(UPSERT).
        // we need the conversation_id to save the context.
        let _ = self
            .storage
            .save(
                "app_app",
                &ExecutionState { app: app.clone(), action: action.clone() },
            )
            .await;

        let (app, commands) = app.run(action)?;
        *guard = app;
        drop(guard);

        join_all(commands.into_iter().map(|command| {
            let executor = executor.clone();
            async move {
                let _: Result<(), A::Error> = async move {
                    let mut stream = executor.clone().execute(&command).await?;
                    while let Some(action) = stream.next().await {
                        let this = self.clone();
                        let executor = executor.clone();
                        // NOTE: The `execute` call needs to run sequentially. Executing it
                        // asynchronously would disrupt the order of `toolUse` content, leading to
                        // mixed-up.
                        this.execute(action?, executor).await?;
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
