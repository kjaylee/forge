use std::sync::Arc;

use forge_domain::{Description, ToolCallService};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::pending_questions::QuestionCoordinator;

/// Represents a question that requires a text response from the user.
/// This is used when the LLM needs to ask the user a question that requires a
/// text response.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TextQuestion {
    /// The question to be presented to the user
    pub question: String,
}

/// Represents a question that requires a boolean choice between two options.
/// This is used when the LLM needs to ask the user a question that requires a
/// binary choice.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct BooleanQuestion {
    /// The question to be presented to the user
    pub question: String,
    /// The first choice for the question
    pub option_one: String,
    /// The second choice for the question
    pub option_two: String,
}

/// Represents different types of questions that the LLM can ask the user.
/// This enum allows the LLM to request either free-form text input or
/// a choice between two options.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase", tag = "type")]
pub enum Question {
    /// A question requiring free-form text input
    Text(TextQuestion),
    /// A question requiring a choice between two options
    Boolean(BooleanQuestion),
}

#[derive(Deserialize, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct AskFollowUpQuestionInput {
    /// The question to ask the user. This should be a clear, specific question
    /// that addresses the information you need.
    pub question: Question,
}

/// Ask the user a question to gather additional information needed to complete
/// the task. This is useful when you need clarification or additional details
/// from the user.
#[derive(Clone, Description)]
pub struct AskFollowUpQuestion {
    pending_questions: Arc<QuestionCoordinator>,
}

impl AskFollowUpQuestion {
    pub fn new(pending_questions: Arc<QuestionCoordinator>) -> Self {
        Self { pending_questions }
    }
}

#[async_trait::async_trait]
impl ToolCallService for AskFollowUpQuestion {
    type Input = AskFollowUpQuestionInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let answer = self
            .pending_questions
            .ask_question(&input.question, None)
            .await
            .map_err(|e| e.to_string())?;
        Ok(answer)
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct AgentQuestion {
    pub id: String,
    pub question: String,
}

impl TryFrom<&Question> for AgentQuestion {
    type Error = String;
    fn try_from(value: &Question) -> Result<Self, Self::Error> {
        let question = serde_json::to_string(&value).map_err(|e| e.to_string())?;
        let id = uuid::Uuid::new_v4().to_string();
        Ok(AgentQuestion { question, id })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_ask_followup_question() {
        let pending_questions = Arc::new(QuestionCoordinator::default());
        let ask = AskFollowUpQuestion::new(pending_questions.clone());

        // Create the subscriber before sending any messages
        let mut receiver = pending_questions.sender.subscribe();

        // Send the question in a separate task
        let ask_handle = tokio::spawn({
            let ask = ask.clone();
            async move {
                let result = ask
                    .call(AskFollowUpQuestionInput {
                        question: Question::Text(TextQuestion {
                            question: "What is your favorite color?".to_string(),
                        }),
                    })
                    .await
                    .unwrap();
                assert_eq!(result, "Blue");
            }
        });

        // Handle the response in main task
        let question = receiver.recv().await.unwrap();
        pending_questions
            .submit_answer(question.id, "Blue".to_string())
            .await
            .unwrap();

        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_ask_followup_boolean_question() {
        let pending_questions = Arc::new(QuestionCoordinator::default());
        let ask = AskFollowUpQuestion::new(pending_questions.clone());

        // Create the subscriber before sending any messages
        let mut receiver = pending_questions.sender.subscribe();

        // Send the question in a separate task
        let ask_handle = tokio::spawn({
            let ask = ask.clone();
            async move {
                let _result = ask
                    .call(AskFollowUpQuestionInput {
                        question: Question::Boolean(BooleanQuestion {
                            question: "Do you like blue?".to_string(),
                            option_one: "Yes".to_string(),
                            option_two: "No".to_string(),
                        }),
                    })
                    .await
                    .unwrap();
                assert_eq!(_result, "Yes".to_string());
            }
        });

        // Handle the response in main task
        let question = receiver.recv().await.unwrap();
        pending_questions
            .submit_answer(question.id, "Yes".to_string())
            .await
            .unwrap();

        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }
}
