use forge_domain::Description;
use forge_domain::ToolCallService;
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc};
use tokio::sync::broadcast;
use tokio::sync::oneshot;
use tokio::sync::RwLock;

/// Represents a question that requires a text response from the user.
/// This is used when the LLM needs free-form text input.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TextQuestion {
    /// The question to be presented to the user
    pub question: String,
}

/// Represents a question that requires a boolean choice between two options.
/// This is used when the LLM needs the user to choose between two alternatives.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct BooleanQuestion {
    /// The question to be presented to the user
    pub question: String,
    /// The first choice option
    pub option_one: String,
    /// The second choice option
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
    pending_questions: Arc<PendingQuestions>,
}

impl AskFollowUpQuestion {
    pub fn new(pending_questions: Arc<PendingQuestions>) -> Self {
        Self { pending_questions }
    }
}

#[async_trait::async_trait]
impl ToolCallService for AskFollowUpQuestion {
    type Input = AskFollowUpQuestionInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let rx = self
            .pending_questions
            .submit_question(&input.question)
            .await?;
        // wait for the user to answer the question
        let answer = rx.await.map_err(|e| e.to_string())?;
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

/// Manages pending questions waiting for user responses
pub struct PendingQuestions {
    pub sender: broadcast::Sender<AgentQuestion>,
    pub questions: Arc<RwLock<HashMap<String, oneshot::Sender<String>>>>,
}

impl Default for PendingQuestions {
    fn default() -> Self {
        let (sender, _) = broadcast::channel(1);
        Self { sender, questions: Arc::new(RwLock::new(HashMap::new())) }
    }
}

impl PendingQuestions {
    pub async fn submit_question(
        &self,
        question: &Question,
    ) -> Result<oneshot::Receiver<String>, String> {
        let (tx, rx) = oneshot::channel();
        let question: AgentQuestion = question.try_into()?;
        self.questions.write().await.insert(question.id.clone(), tx);

        // Send the question to the client.
        self.sender.send(question).expect("Failed to send question");

        Ok(rx)
    }

    /// Submit an answer for a question by its ID
    pub async fn submit_answer(&self, id: String, answer: String) -> Result<(), String> {
        let mut questions = self.questions.write().await;
        if let Some(tx) = questions.remove(&id) {
            tx.send(answer)
                .map_err(|_| "Failed to send answer".to_string())
        } else {
            Err("Question not found".to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_ask_followup_question() {
        let pending_questions = Arc::new(PendingQuestions::default());
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
        let pending_questions = Arc::new(PendingQuestions::default());
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

    #[test]
    fn test_question_serialization() {
        let text_q = Question::Text(TextQuestion { question: "What's your name?".to_string() });
        let bool_q = Question::Boolean(BooleanQuestion {
            question: "Do you agree?".to_string(),
            option_one: "Yes".to_string(),
            option_two: "No".to_string(),
        });

        let text_json = serde_json::to_string_pretty(&text_q).unwrap();
        let bool_json = serde_json::to_string_pretty(&bool_q).unwrap();

        println!("Text question: {}", text_json);

        assert!(text_json.contains("text"));
        assert!(bool_json.contains("boolean"));
    }
}
