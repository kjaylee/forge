use std::sync::Arc;

use forge_domain::{Description, QuestionCoordinatorService, QuestionIdentifier, ToolCallService};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum QuestionType {
    Text,
    Boolean,
}

#[derive(Deserialize, Serialize, JsonSchema)]
pub struct AskFollowUpQuestionInput {
    /// The question to ask the user. This should be a clear, specific question
    /// that addresses the information you need.
    pub question: String,
    /// The type of the question. This determines whether the question expects
    /// a textual answer or a boolean response (e.g., true/false or yes/no).
    /// type can be either "text" or "boolean".
    pub r#type: QuestionType,
    /// The list of available choices for the user. This is only required for
    /// boolean questions, where the user must choose between two options
    /// (e.g., "Yes" or "No").
    pub choices: Option<Vec<String>>,
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
        match input.r#type {
            QuestionType::Text => {
                if input.choices.is_some() {
                    return Err("Choices are not allowed for text questions".to_string());
                }
            }
            QuestionType::Boolean => {
                if input.choices.as_ref().is_none_or(|c| c.is_empty()) {
                    return Err(
                        "Choices are required and cannot be empty for boolean questions"
                            .to_string(),
                    );
                }
            }
        }

        let agent_question = AgentQuestion::from(input);
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub choices: Option<Vec<String>>,
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

impl From<AskFollowUpQuestionInput> for AgentQuestion {
    fn from(value: AskFollowUpQuestionInput) -> Self {
        let question = value.question;
        let choices = value.choices;
        let id = uuid::Uuid::new_v4().to_string();
        AgentQuestion { question, id, choices }
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
                        question: "What is your favorite color?".to_string(),
                        r#type: QuestionType::Text,
                        choices: None,
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
                        question: "Do you like blue?".to_string(),
                        r#type: QuestionType::Boolean,
                        choices: Some(vec!["Yes".to_string(), "No".to_string()]),
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

    #[tokio::test]
    async fn test_choices_required_for_boolean_question() {
        let question_coordinator = Arc::new(Service::question_coordinator());
        let ask = AskFollowUpQuestion::new(question_coordinator.clone());

        // Send the question in a separate task
        let ask_handle = tokio::spawn({
            let ask = ask.clone();
            async move {
                // test 1: check when choices are not provided.
                let result = ask
                    .call(AskFollowUpQuestionInput {
                        question: "What is your favorite color?".to_string(),
                        r#type: QuestionType::Boolean,
                        choices: None,
                    })
                    .await;
                assert!(result.is_err());

                // test 2: check when choices array is provided but it's empty.
                let result = ask
                    .call(AskFollowUpQuestionInput {
                        question: "What is your favorite color?".to_string(),
                        r#type: QuestionType::Boolean,
                        choices: Some(vec![]),
                    })
                    .await;
                assert!(result.is_err());
            }
        });
        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_text_question_shouldnt_have_choices() {
        let question_coordinator = Arc::new(Service::question_coordinator());
        let ask = AskFollowUpQuestion::new(question_coordinator.clone());

        // Send the question in a separate task
        let ask_handle = tokio::spawn({
            let ask = ask.clone();
            async move {
                let result = ask
                    .call(AskFollowUpQuestionInput {
                        question: "What is your favorite color?".to_string(),
                        r#type: QuestionType::Text,
                        choices: Some(vec!["Blue".to_string(), "Red".to_string()]),
                    })
                    .await;
                assert!(result.is_err());
            }
        });
        // Ensure the ask task completes
        ask_handle.await.unwrap();
    }
}
