use serde::de::DeserializeOwned;
use serde::Serialize;

#[derive(Debug)]
pub enum CoordinatorError {
    QuestionSendError(String),
    AnswerSendError(String),
    QuestionNotFound(String),
    QuestionConversion(String),
}
impl std::fmt::Display for CoordinatorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoordinatorError::QuestionSendError(question_id) => {
                write!(f, "Failed to send question with ID: {}", question_id)
            }
            CoordinatorError::AnswerSendError(question_id) => {
                write!(
                    f,
                    "Failed to send answer for question with ID: {}",
                    question_id
                )
            }
            CoordinatorError::QuestionNotFound(question_id) => {
                write!(f, "Question with ID not found: {}", question_id)
            }
            CoordinatorError::QuestionConversion(question_id) => {
                write!(f, "Failed to convert question with ID: {}", question_id)
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
