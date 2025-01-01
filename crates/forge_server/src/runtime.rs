use std::sync::Arc;

use forge_provider::ResultStream;
use futures::future::join_all;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use tokio::sync::Mutex;
use tokio_stream::StreamExt;

use crate::{app::App, Storage};

pub trait Identifier {
    fn id(&self) -> &str;
}

impl Identifier for App {
    fn id(&self) -> &str {
        self.conversation_id()
            .expect("at this point conversation_id should be set")
    }
}

pub trait Application: Send + Sync + Sized + Clone {
    type Action: Send + Sync;
    type Error: Send;
    type Command: Send;
    fn run(
        &mut self,
        action: impl Into<Self::Action>,
    ) -> std::result::Result<Vec<Self::Command>, Self::Error>;

    #[allow(unused)]
    fn run_seq(&mut self, actions: Vec<Self::Action>) -> Result<Vec<Self::Command>, Self::Error>
    where
        Self::Action: Clone,
    {
        let mut commands = Vec::new();
        for action in actions {
            commands.extend(self.run(action.clone())?)
        }

        Ok(commands)
    }
}

#[derive(Clone)]
pub struct ApplicationRuntime<S: Storage> {
    storage: Arc<S>,
}

impl<S: Storage> ApplicationRuntime<S> {
    pub fn new(storage: Arc<S>) -> Self {
        Self { storage }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionContext<A, B> {
    pub app: A,
    pub action: B,
}

impl<S: Storage + 'static> ApplicationRuntime<S> {
    #[async_recursion::async_recursion]
    pub async fn execute<'a, A: Application + Serialize + DeserializeOwned + Identifier>(
        &'a self,
        base_app: Arc<Mutex<A>>,
        action: A::Action,
        executor: Arc<
            impl Executor<Command = A::Command, Action = A::Action, Error = A::Error> + 'static,
        >,
    ) -> std::result::Result<(), A::Error>
    where
        A::Action: Serialize + DeserializeOwned + Clone,
    {
        let mut guard = base_app.lock().await;
        let commands = guard.run(action.clone())?;

        // Save the current state of the app.
        let _ = self
            .storage
            .save(guard.id(), &ExecutionContext { app: guard.clone(), action })
            .await;

        drop(guard);

        join_all(commands.into_iter().map(|command| {
            let executor = executor.clone();
            let app = base_app.clone();
            async move {
                let _: Result<(), A::Error> = async move {
                    let mut stream = executor.clone().execute(&command).await?;
                    while let Some(action) = stream.next().await {
                        let this = self.clone();
                        let executor = executor.clone();
                        let app = app.clone();
                        // NOTE: The `execute` call needs to run sequentially. Executing it
                        // asynchronously would disrupt the order of `toolUse` content, leading to
                        // mixed-up.
                        this.execute(app, action?, executor).await?;
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
