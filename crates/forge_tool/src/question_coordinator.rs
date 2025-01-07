use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use tokio::sync::{broadcast, oneshot, RwLock};
use tokio::time::timeout;

use crate::ask::AgentQuestion;

#[derive(Debug)]
pub enum CoordinatorError {
    QuestionSendError,
    AnswerSendError,
    QuestionNotFound,
    AnswerTimeout,
    QuestionConversion(String),
}

impl std::fmt::Display for CoordinatorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoordinatorError::QuestionSendError => write!(f, "Failed to send question"),
            CoordinatorError::AnswerSendError => write!(f, "Failed to send answer"),
            CoordinatorError::QuestionNotFound => write!(f, "Question not found"),
            CoordinatorError::AnswerTimeout => write!(f, "Answer timeout"),
            CoordinatorError::QuestionConversion(e) => {
                write!(f, "Failed to convert question: {}", e)
            }
        }
    }
}

/// Coordinates asynchronous question-answer interactions between an agent and a
/// client
pub struct QuestionCoordinator {
    pub sender: broadcast::Sender<AgentQuestion>,
    questions: Arc<RwLock<HashMap<String, oneshot::Sender<String>>>>,
}

impl Default for QuestionCoordinator {
    fn default() -> Self {
        let (sender, _) = broadcast::channel(1);
        Self { sender, questions: Arc::new(RwLock::new(HashMap::new())) }
    }
}

impl QuestionCoordinator {
    /// Ask a question and wait for the answer with an optional timeout
    pub async fn ask_question<Q>(
        &self,
        question: &Q,
        timeout_duration: Option<Duration>,
    ) -> Result<String, CoordinatorError>
    where
        for<'a> &'a Q: TryInto<AgentQuestion>,
        for<'a> <&'a Q as TryInto<AgentQuestion>>::Error: ToString,
    {
        let (tx, rx) = oneshot::channel();
        let question: AgentQuestion = question
            .try_into()
            .map_err(|e| CoordinatorError::QuestionConversion(e.to_string()))?;

        self.questions.write().await.insert(question.id.clone(), tx);

        self.sender
            .send(question)
            .map_err(|_| CoordinatorError::QuestionSendError)?;

        match timeout_duration {
            Some(duration) => timeout(duration, rx)
                .await
                .map_err(|_| CoordinatorError::AnswerTimeout)?
                .map_err(|_| CoordinatorError::AnswerSendError),
            None => rx.await.map_err(|_| CoordinatorError::AnswerSendError),
        }
    }

    /// Submit an answer for a question by its ID
    pub async fn submit_answer(&self, id: String, answer: String) -> Result<(), CoordinatorError> {
        let mut questions = self.questions.write().await;
        if let Some(tx) = questions.remove(&id) {
            tx.send(answer)
                .map_err(|_| CoordinatorError::AnswerSendError)
        } else {
            Err(CoordinatorError::QuestionNotFound)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::time::Duration;

    use super::{CoordinatorError, QuestionCoordinator};
    use crate::ask::AgentQuestion;

    #[derive(Debug)]
    struct MockQuestion {
        id: String,
        text: String,
    }

    impl TryFrom<&MockQuestion> for AgentQuestion {
        type Error = String;

        fn try_from(q: &MockQuestion) -> Result<Self, Self::Error> {
            Ok(AgentQuestion { id: q.id.clone(), question: q.text.clone() })
        }
    }

    #[tokio::test]
    async fn test_ask_question_success() {
        let coordinator = Arc::new(QuestionCoordinator::default());
        let question =
            MockQuestion { id: "test-id".to_string(), text: "test-question".to_string() };

        // Set up the subscriber first
        let coordinator_clone = coordinator.clone();
        let mut receiver = coordinator_clone.sender.subscribe();

        // Then spawn the task that will handle the answer
        let coordinator_clone = coordinator.clone();
        tokio::spawn(async move {
            if let Ok(q) = receiver.recv().await {
                coordinator_clone
                    .submit_answer(q.id, "test-answer".to_string())
                    .await
                    .unwrap();
            }
        });

        let result = coordinator.ask_question(&question, None).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "test-answer");
    }

    #[tokio::test]
    async fn test_ask_question_timeout() {
        let coordinator = Arc::new(QuestionCoordinator::default());

        let question =
            MockQuestion { id: "test-id".to_string(), text: "test-question".to_string() };

        // Create a subscriber to prevent QuestionSendError
        let _receiver = coordinator.sender.subscribe();

        let result = coordinator
            .ask_question(&question, Some(Duration::from_millis(100)))
            .await;

        assert!(matches!(result, Err(CoordinatorError::AnswerTimeout)));
    }

    #[tokio::test]
    async fn test_submit_answer_question_not_found() {
        let coordinator = QuestionCoordinator::default();
        let result = coordinator
            .submit_answer("nonexistent-id".to_string(), "answer".to_string())
            .await;

        assert!(matches!(result, Err(CoordinatorError::QuestionNotFound)));
    }
}
