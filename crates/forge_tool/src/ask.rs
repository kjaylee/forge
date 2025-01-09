use std::sync::Arc;

use forge_domain::{Description, QuestionCoordinatorService, QuestionIdentifier, ToolCallService};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

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
    question_coordinator:
        Arc<dyn QuestionCoordinatorService<Question = AgentQuestion, Answer = Answer>>,
}

impl AskFollowUpQuestion {
    pub fn new(
        question_coordinator: Arc<
            dyn QuestionCoordinatorService<Question = AgentQuestion, Answer = Answer>,
        >,
    ) -> Self {
        Self { question_coordinator }
    }
}

#[async_trait::async_trait]
impl ToolCallService for AskFollowUpQuestion {
    type Input = AskFollowUpQuestionInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let agent_question = AgentQuestion::try_from(&input.question)?;
        let answer = self
            .question_coordinator
            .ask_question(agent_question)
            .await
            .map_err(|e| e.to_string())?;
        Ok(answer.answer)
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct AgentQuestion {
    pub id: String,
    pub question: String,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Answer {
    pub id: String,
    pub answer: String,
}

impl QuestionIdentifier for Answer {
    type QuestionId = String;
    fn question_id(&self) -> Self::QuestionId {
        self.id.clone()
    }
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
mod test {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::Service;

    #[tokio::test]
    async fn test_ask_followup_question() {
        let question_coordinator = Arc::new(Service::question_coordinator());
        let ask = AskFollowUpQuestion::new(question_coordinator.clone());

        // Create the subscriber before sending any messages
        let mut receiver = question_coordinator.subscribe().await;

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
        question_coordinator
            .submit_answer(Answer { id: question.id, answer: "Blue".to_string() })
            .await
            .unwrap();

        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_ask_followup_boolean_question() {
        let question_coordinator = Arc::new(Service::question_coordinator());
        let ask = AskFollowUpQuestion::new(question_coordinator.clone());

        // Create the subscriber before sending any messages
        let mut receiver = question_coordinator.subscribe().await;

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
        question_coordinator
            .submit_answer(Answer { id: question.id, answer: "Yes".to_string() })
            .await
            .unwrap();

        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }
}
