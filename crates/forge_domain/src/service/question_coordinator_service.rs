use serde::{de::DeserializeOwned, Serialize};

#[derive(Debug)]
pub enum CoordinatorError {
    QuestionSendError,
    AnswerSendError,
    QuestionNotFound,
    QuestionConversion(String),
}

impl std::fmt::Display for CoordinatorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoordinatorError::QuestionSendError => write!(f, "Failed to send question"),
            CoordinatorError::AnswerSendError => write!(f, "Failed to send answer"),
            CoordinatorError::QuestionNotFound => write!(f, "Question not found"),
            CoordinatorError::QuestionConversion(e) => {
                write!(f, "Failed to convert question: {}", e)
            }
        }
    }
}

pub trait QuestionIdentifier {
    type QuestionId;
    fn question_id(&self) -> Self::QuestionId;
}

#[async_trait::async_trait]
pub trait QuestionCoordinatorService: Send + Sync {
    type Question: Serialize;
    type Answer: DeserializeOwned + QuestionIdentifier;
    async fn subscribe(&self) -> tokio::sync::broadcast::Receiver<Self::Question>;
    async fn ask_question(
        &self,
        question: Self::Question,
    ) -> Result<Self::Answer, CoordinatorError>;
    async fn submit_answer(&self, answer: Self::Answer) -> Result<(), CoordinatorError>;
}
