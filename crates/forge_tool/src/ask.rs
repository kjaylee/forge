use forge_domain::{Description, ToolCallService};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

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
pub struct AskFollowUpQuestionInput {
    /// The question to ask the user. This should be a clear, specific question
    /// that addresses the information you need.
    pub question: Question,
}

/// Ask the user a question to gather additional information needed to complete
/// the task. This tool should be used when you encounter ambiguities, need
/// clarification, or require more details to proceed effectively. It allows for
/// interactive problem-solving by enabling direct communication with the user.
#[derive(Description)]
pub struct AskFollowUpQuestion;

#[async_trait::async_trait]
impl ToolCallService for AskFollowUpQuestion {
    type Input = AskFollowUpQuestionInput;
    type Output = String;

    async fn call(&self, _input: Self::Input) -> Result<Self::Output, String> {
        Ok("".to_string())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[tokio::test]
    async fn test_ask_followup_question() {
        let ask = AskFollowUpQuestion;
        let _result = ask
            .call(AskFollowUpQuestionInput {
                question: Question::Text(TextQuestion {
                    question: "What is your favorite color?".to_string(),
                }),
            })
            .await
            .unwrap();
        // assert_eq!(result, "Question: What is your favorite color?");
    }

    #[tokio::test]
    async fn test_ask_followup_boolean_question() {
        let ask = AskFollowUpQuestion;
        let _result = ask
            .call(AskFollowUpQuestionInput {
                question: Question::Boolean(BooleanQuestion {
                    question: "Do you like cats?".to_string(),
                    option_one: "Yes".to_string(),
                    option_two: "No".to_string(),
                }),
            })
            .await
            .unwrap();
    }

    #[test]
    fn test_description() {
        assert!(AskFollowUpQuestion::description().len() > 100)
    }
}
