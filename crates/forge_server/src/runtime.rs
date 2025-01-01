use std::sync::Arc;

use forge_provider::ResultStream;
use futures::future::join_all;
use serde::de::DeserializeOwned;
use serde::Serialize;
use tokio::sync::Mutex;
use tokio_stream::StreamExt;

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
pub struct ApplicationRuntime;

impl ApplicationRuntime {
    #[async_recursion::async_recursion]
    pub async fn execute<'a, A>(
        &'a self,
        app: Arc<Mutex<A>>,
        action: A::Action,
        executor: Arc<
            impl Executor<Command = A::Command, Action = A::Action, Error = A::Error> + 'static,
        >,
    ) -> std::result::Result<A::Action, A::Error>
    where
        A: Application + Serialize + DeserializeOwned,
        A::Action: Clone,
    {
        let mut guard = app.lock().await;
        let commands = guard.run(action.clone())?;
        drop(guard);

        join_all(commands.into_iter().map(|command| {
            let executor = executor.clone();
            let app = app.clone();
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

        Ok(action)
    }
}

#[async_trait::async_trait]
pub trait Executor: Send + Sync {
    type Command;
    type Action;
    type Error;
    async fn execute(&self, command: &Self::Command) -> ResultStream<Self::Action, Self::Error>;
}
