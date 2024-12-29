use std::collections::HashMap;

use anyhow::Result;
use colorize::AnsiColor;
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{Description, ToolTrait};

/// A flexible, iterative reasoning framework for multi-step problem analysis.
/// 
/// ## Purpose
/// Use this structure to capture a series of "thoughts" (or reasoning steps) that
/// can be expanded, revised, or branched off. It is designed to guide and track the
/// chain-of-thought behind solving complex or partially defined problems.
///
/// This framework is particularly suitable for:
/// - Decomposing complex tasks into multiple steps
/// - Maintaining context across iterative reasoning passes
/// - Revising earlier thought processes without losing the entire history
/// - Splitting reasoning into multiple branches when exploring alternative solutions
/// - Tracking confidence levels as you generate and verify hypotheses
///
/// ## Key Features
/// - **Adjustable Thought Count**: You can increase or decrease `total_thoughts`
///   at any point to accommodate unexpected complexity.
/// - **Revisions**: Mark any step as a revision (`is_revision`) of a previous
///   step (`revises_thought`).
/// - **Branching**: Create alternative solution paths by forking from a specific
///   thought (`branch_from_thought`) and labeling the branch with `branch_id`.
/// - **Iterative Confidence**: Optionally store and update a `solution_confidence`
///   rating for each thought as analysis progresses.
/// - **Solution Hypothesis & Verification**: Store partial or final solution
///   hypotheses, then verify them step-by-step, and repeat until the solution
///   is reached (`solution_reached`).
///
/// ## Usage in LLM Workflows
/// 1. **Initialize**: Start with a `Think` object, specifying an initial guess for
///    `total_thoughts`.
/// 2. **Add Thoughts**: Append entries to `thought_history` as you break down
///    the problem and explore solutions.
/// 3. **Revise / Branch**: If you realize a mistake or want to explore a new line
///    of reasoning, mark the thought with `is_revision` and `revises_thought` or
///    branch out with `branch_from_thought` and `branch_id`.
/// 4. **Check Completion**: If `solution_reached` is true and `next_thought_needed`
///    is false, the reasoning is considered complete and an answer can be provided.
/// 5. **Confidence Tracking**: At each step, optionally update `solution_confidence`
///    to reflect how certain you are in the emerging solution.
/// 6. **Final Answer**: When done, the last thought in `thought_history` should
///    contain the correct or best solution found.
///
/// ## Fields
/// - **thought_history**: A list of `ThoughtData` representing each step in your
///   iterative reasoning process.
/// - **branches**: A mapping from branch IDs to alternate `ThoughtData` sequences.
///   Helpful when the solution involves exploring or comparing parallel solution
///   paths.
/// - **solution_reached**: A boolean indicating if you have arrived at a final,
///   validated solution.
///
/// For usage examples, see tests or demonstration code where `Think` is used to
/// hold state across an interactive or iterative problem-solving session.
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
    fn validate_thought_data(&self, mut input: ThoughtData) -> Result<ThoughtData> {
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

    fn process_thought(&mut self, input: ThoughtData) -> Result<ThoughtResult> {
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

#[async_trait::async_trait]
impl ToolTrait for Think {
    type Input = ThoughtData;
    type Output = ThoughtResult;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let mut thinker = self.clone();
        let thought_result = thinker.process_thought(input).map_err(|e| e.to_string())?;
        Ok(thought_result)
    }
}
