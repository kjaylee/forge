use std::collections::HashMap;

use anyhow::Result;
use colorize::AnsiColor;
use forge_domain::{NamedTool, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Framework for tracking and managing problem-solving steps. Supports
/// step-by-step task breakdown, revisions, branching, and confidence tracking.
/// Use `total_thoughts` for complexity, `revises_thought` for revisions,
/// `branch_from_thought` for branching, and `solution_confidence` for progress.
/// Track steps in `thought_history`, manage alternate paths in `branches`, mark
/// completion with `solution_reached
#[derive(Clone, Default, ToolDescription)]
pub struct Think {
    thought_history: Vec<ThoughtInput>,
    branches: HashMap<String, Vec<ThoughtInput>>,
    solution_reached: bool,
}

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ThoughtInput {
    /// Description of current thought/reasoning step
    pub thought: String,
    /// Indicates if another thought is needed
    pub next_thought_needed: bool,
    /// Number of current thought/step
    pub thought_number: i32,
    /// Total thoughts/steps expected for solution
    pub total_thoughts: i32,
    /// Indicates if this is a revision
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_revision: Option<bool>,
    /// Number of thought being revised
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revises_thought: Option<i32>,
    /// Parent thought number for this branch
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_from_thought: Option<i32>,
    /// Unique branch identifier
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_id: Option<String>,
    /// Indicates if more thoughts needed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub needs_more_thoughts: Option<bool>,
    /// Solution confidence (0.0-1.0)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solution_confidence: Option<f32>,
}

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ThoughtResult {
    pub thought_number: i32,
    pub total_thoughts: i32,
    pub next_thought_needed: bool,
    pub solution_reached: bool,
    pub solution_confidence: f32,
    pub branches: Vec<String>,
    pub thought_history_length: usize,
}

impl Think {
    fn validate_thought_data(&self, mut input: ThoughtInput) -> Result<ThoughtInput> {
        if input.thought_number <= 0 {
            return Err(anyhow::anyhow!("Invalid thoughtNumber: must be positive"));
        }
        if input.total_thoughts <= 0 {
            return Err(anyhow::anyhow!("Invalid totalThoughts: must be positive"));
        }

        // If no confidence is provided, calculate it based on progress
        if input.solution_confidence.is_none() {
            input.solution_confidence =
                Some(input.thought_number as f32 / input.total_thoughts as f32);
        }

        Ok(input)
    }

    fn format_thought(&self, thought_data: &ThoughtInput) -> String {
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

    fn process_thought(&mut self, input: ThoughtInput) -> Result<ThoughtResult> {
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

        Ok(ThoughtResult {
            thought_number: thought_data.thought_number,
            total_thoughts: thought_data.total_thoughts,
            next_thought_needed: thought_data.next_thought_needed,
            solution_reached: self.solution_reached,
            solution_confidence: thought_data.solution_confidence.unwrap_or(0.0),
            branches: self.branches.keys().cloned().collect(),
            thought_history_length: self.thought_history.len(),
        })
    }
}

impl NamedTool for Think {
    fn tool_name(&self) -> ToolName {
        ToolName::new("think_step")
    }
}

#[async_trait::async_trait]
impl ToolCallService for Think {
    type Input = ThoughtInput;
    type Output = ThoughtResult;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let mut thinker = self.clone();
        let thought_result = thinker.process_thought(input).map_err(|e| e.to_string())?;
        Ok(thought_result)
    }
}
