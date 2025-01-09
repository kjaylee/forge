use std::{collections::HashMap, sync::Arc};

use forge_domain::{CoordinatorError, QuestionCoordinatorService, QuestionIdentifier};
use tokio::sync::{broadcast, oneshot, RwLock};

use crate::{
    ask::{AgentQuestion, Answer},
    Service,
};

struct QuestionCoordinator {
    pub sender: broadcast::Sender<AgentQuestion>,
    pub questions: Arc<RwLock<HashMap<String, oneshot::Sender<Answer>>>>,
}

impl Default for QuestionCoordinator {
    fn default() -> Self {
        let (sender, _) = broadcast::channel(1);
        Self { sender, questions: Arc::new(RwLock::new(HashMap::new())) }
    }
}

impl Service {
    pub fn question_coordinator(
    ) -> impl  QuestionCoordinatorService<Question = AgentQuestion, Answer = Answer> {
        QuestionCoordinator::default()
    }
}

#[async_trait::async_trait]
impl QuestionCoordinatorService for QuestionCoordinator {
    type Question = AgentQuestion;
    type Answer = Answer;

    async fn subscribe(&self) -> broadcast::Receiver<Self::Question> {
        self.sender.subscribe()
    }

    async fn ask_question(
        &self,
        question: Self::Question,
    ) -> Result<Self::Answer, CoordinatorError> {
        let (tx, rx) = oneshot::channel();
        self.questions.write().await.insert(question.id.clone(), tx);
        self.sender
            .send(question)
            .map_err(|_| CoordinatorError::QuestionSendError)?;
        rx.await.map_err(|_| CoordinatorError::QuestionSendError)
    }

    async fn submit_answer(&self, answer: Self::Answer) -> Result<(), CoordinatorError> {
        let question_id = answer.question_id();
        let tx = self
            .questions
            .write()
            .await
            .remove(&question_id)
            .ok_or(CoordinatorError::QuestionNotFound)?;
        tx.send(answer)
            .map_err(|_| CoordinatorError::AnswerSendError)
    }
}
