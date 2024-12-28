use std::collections::HashMap;

use anyhow::Result;
use colorize::AnsiColor;
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{Description, ToolTrait};

/// A flexible thinking tool that helps analyze problems through an adaptive process.
///
/// This tool allows for multi-step problem solving with the ability to:
/// - Break down complex problems
/// - Revise and branch thoughts
/// - Track solution confidence
/// - Dynamically adjust thinking strategy
#[derive(Clone, Default, Description)]
pub struct Think {
    thought_history: Vec<ThoughtData>,
    branches: HashMap<String, Vec<ThoughtData>>,
    solution_reached: bool,
}

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ThoughtData {
    pub thought: String,
    pub next_thought_needed: bool,
    pub thought_number: i32,
    pub total_thoughts: i32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_revision: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revises_thought: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_from_thought: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub needs_more_thoughts: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solution_confidence: Option<f32>,
}

impl Think {
    fn validate_thought_data(&self, input: ThoughtData) -> Result<ThoughtData> {
        if input.thought_number <= 0 {
            return Err(anyhow::anyhow!("Invalid thoughtNumber: must be positive"));
        }
        if input.total_thoughts <= 0 {
            return Err(anyhow::anyhow!("Invalid totalThoughts: must be positive"));
        }

        Ok(ThoughtData {
            thought: input.thought,
            thought_number: input.thought_number,
            total_thoughts: input.total_thoughts,
            next_thought_needed: input.next_thought_needed,
            is_revision: input.is_revision,
            revises_thought: input.revises_thought,
            branch_from_thought: input.branch_from_thought,
            branch_id: input.branch_id,
            needs_more_thoughts: input.needs_more_thoughts,
            solution_confidence: input.solution_confidence.or(Some(0.0)),
        })
    }

    fn format_thought(&self, thought_data: &ThoughtData) -> String {
        let (prefix, context) = match (thought_data.is_revision, &thought_data.branch_from_thought)
        {
            (Some(true), _) => (
                "🔄 Revision".yellow().to_string(),
                format!(
                    " (revising thought {})",
                    thought_data.revises_thought.unwrap_or(0)
                ),
            ),
            (_, Some(branch)) => (
                "🌿 Branch".green().to_string(),
                format!(
                    " (from thought {}, ID: {})",
                    branch,
                    thought_data.branch_id.as_ref().unwrap_or(&String::new())
                ),
            ),
            _ => ("💭 Thought".blue().to_string(), String::new()),
        };

        let header = format!(
            "{} {}/{}{} (Confidence: {:.2}%)",
            prefix, 
            thought_data.thought_number, 
            thought_data.total_thoughts, 
            context,
            thought_data.solution_confidence.unwrap_or(0.0) * 100.0
        );
        let border_len = header.len().max(thought_data.thought.len()) + 4;
        let border = "─".repeat(border_len);

        let thought_data = format!("{:width$}", thought_data.thought, width = border_len - 2);

        format!(
            "\n┌{}┐\n│ {} │\n├{}┤\n│ {} │\n└{}┘",
            border, header, border, thought_data, border
        )
    }

    fn process_thought(&mut self, input: ThoughtData) -> Result<serde_json::Value> {
        let mut thought_data = self.validate_thought_data(input)?;

        // Adjust total thoughts if needed
        if thought_data.thought_number > thought_data.total_thoughts {
            thought_data.total_thoughts = thought_data.thought_number;
        }

        // Evaluate solution confidence
        if let Some(confidence) = thought_data.solution_confidence {
            if confidence >= 0.8 {
                self.solution_reached = true;
                thought_data.next_thought_needed = false;
            }
        }

        // Terminate thinking if max thoughts reached or solution found
        if thought_data.thought_number >= thought_data.total_thoughts || self.solution_reached {
            thought_data.next_thought_needed = false;
        }

        // Always allow at least one thought to be processed
        if self.thought_history.is_empty() {
            thought_data.next_thought_needed = true;
        }

        self.thought_history.push(thought_data.clone());

        // Branch handling remains the same
        if let (Some(_), Some(branch_id)) =
            (thought_data.branch_from_thought, &thought_data.branch_id)
        {
            self.branches
                .entry(branch_id.clone())
                .or_default()
                .push(thought_data.clone());
        }

        eprintln!("{}", self.format_thought(&thought_data));

        let result = serde_json::json!({
            "thoughtNumber": thought_data.thought_number,
            "totalThoughts": thought_data.total_thoughts,
            "nextThoughtNeeded": thought_data.next_thought_needed,
            "solutionReached": self.solution_reached,
            "branches": self.branches.keys().collect::<Vec<_>>(),
            "thoughtHistoryLength": self.thought_history.len()
        });

        Ok(result)
    }
}

#[async_trait::async_trait]
impl ToolTrait for Think {
    type Input = ThoughtData;
    type Output = serde_json::Value;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let mut thinker = self.clone();
        let thought_result = thinker.process_thought(input).map_err(|e| e.to_string())?;
        Ok(thought_result)
    }
}
