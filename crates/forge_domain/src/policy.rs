use std::ops::Not;
use std::path::PathBuf;

use glob::Pattern;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Represents different permission levels for policy evaluation
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Permission {
    /// Allow the operation once without further prompts
    AllowOnce,
    /// Disallow the operation once
    DisallowOnce,
    /// Always allow this type of operation
    AllowAlways,
    /// Always disallow this type of operation
    DisallowAlways,
    /// Always confirm before allowing this operation
    Confirm,
}

/// Represents different types of operations that can be controlled by policies
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    /// File write operations with glob pattern matching
    Write { pattern: Pattern },
    /// File read operations with glob pattern matching
    Read { pattern: Pattern },
    /// Command execution with glob pattern matching
    Execute { command: Pattern },
}

/// Represents a policy that can be evaluated against operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Policy {
    /// A simple policy with permission and rule
    Policy { permission: Permission, rule: Rule },
    /// Logical AND of two policies
    And(Box<Policy>, Box<Policy>),
    /// Logical OR of two policies
    Or(Box<Policy>, Box<Policy>),
    /// Logical NOT of a policy
    Not(Box<Policy>),
}

/// Represents an operation that needs policy evaluation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operation {
    /// File write operation
    Write { path: PathBuf },
    /// File read operation
    Read { path: PathBuf },
    /// Command execution
    Execute { command: String },
}

/// Result of policy evaluation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyStatus {
    /// Operation is allowed
    Pass,
    /// Operation is denied
    Fail,
}

/// Errors that can occur during policy evaluation
#[derive(Debug, Error)]
pub enum PolicyError {
    #[error("Invalid glob pattern: {0}")]
    InvalidGlobPattern(String),

    #[error("Policy evaluation failed: {0}")]
    EvaluationFailed(String),

    #[error("No matching rule found for operation")]
    NoMatchingRule,
}

pub type PolicyResult<T> = std::result::Result<T, PolicyError>;

impl Policy {
    /// Create a new simple policy
    pub fn new(permission: Permission, rule: Rule) -> Self {
        Policy::Policy { permission, rule }
    }

    /// Combine two policies with logical AND
    pub fn and(self, other: Policy) -> Self {
        Policy::And(Box::new(self), Box::new(other))
    }

    /// Combine two policies with logical OR
    pub fn or(self, other: Policy) -> Self {
        Policy::Or(Box::new(self), Box::new(other))
    }
}

impl Not for Policy {
    type Output = Self;

    /// Negate a policy using the standard Not trait
    fn not(self) -> Self::Output {
        Policy::Not(Box::new(self))
    }
}

impl Policy {
    /// Evaluate the policy against an operation
    pub fn eval(&self, operation: &Operation) -> bool {
        match self {
            Policy::Policy { permission, rule } => {
                if self.rule_matches(rule, operation) {
                    match permission {
                        Permission::AllowOnce | Permission::AllowAlways => true,
                        Permission::DisallowOnce | Permission::DisallowAlways => false,
                        Permission::Confirm => true, // Simplified: assume user confirms
                    }
                } else {
                    false
                }
            }
            Policy::And(left, right) => left.eval(operation) && right.eval(operation),
            Policy::Or(left, right) => left.eval(operation) || right.eval(operation),
            Policy::Not(policy) => !policy.eval(operation),
        }
    }

    /// Check if a rule matches an operation
    fn rule_matches(&self, rule: &Rule, operation: &Operation) -> bool {
        match (rule, operation) {
            (Rule::Write { pattern }, Operation::Write { path }) => {
                let target_str = path.to_string_lossy();
                pattern.matches(&target_str)
            }
            (Rule::Read { pattern }, Operation::Read { path }) => {
                let target_str = path.to_string_lossy();
                pattern.matches(&target_str)
            }
            (Rule::Execute { command: pattern }, Operation::Execute { command }) => {
                pattern.matches(command)
            }
            _ => false,
        }
    }

    /// Find all rules that match the given operation
    pub fn find_rules(&self, operation: &Operation) -> Vec<Rule> {
        self.collect_matching_rules(operation)
    }

    /// Recursively collect matching rules
    fn collect_matching_rules(&self, operation: &Operation) -> Vec<Rule> {
        match self {
            Policy::Policy { rule, .. } => {
                let mut rules = Vec::default();
                if self.rule_matches(rule, operation) {
                    rules.push(rule.clone());
                }
                return rules;
            }
            Policy::And(left, right) | Policy::Or(left, right) => {
                let mut left_rules = left.collect_matching_rules(operation);
                let right_rules = right.collect_matching_rules(operation);
                left_rules.extend(right_rules);
                return left_rules;
            }
            Policy::Not(policy) => policy.collect_matching_rules(operation),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use pretty_assertions::assert_eq;

    use super::*;

    fn create_write_operation_fixture(path: &str) -> Operation {
        Operation::Write { path: PathBuf::from(path) }
    }

    fn create_read_operation_fixture(path: &str) -> Operation {
        Operation::Read { path: PathBuf::from(path) }
    }

    fn create_execute_operation_fixture(command: &str) -> Operation {
        Operation::Execute { command: command.to_string() }
    }

    #[test]
    fn test_policy_eval_allow_always() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("/**/*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("/home/test.rs");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_policy_eval_disallow_always() {
        let fixture_policy = Policy::new(
            Permission::DisallowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test.rs");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = false;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_policy_eval_no_match() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test.py");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = false;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_policy_and_logic() {
        let fixture_policy1 = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_policy2 = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("test*").unwrap() },
        );
        let fixture_combined = fixture_policy1.and(fixture_policy2);
        let fixture_operation = create_write_operation_fixture("test.rs");

        let actual = fixture_combined.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_policy_or_logic() {
        // allow any .py or .rs file to be written
        let policies = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.py").unwrap() },
        )
        .or(Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        ));
        let fixture_operation = create_write_operation_fixture("test.rs");
        let actual = policies.eval(&fixture_operation);
        let expected = true;
        assert_eq!(actual, expected);

        let fixture_operation = create_write_operation_fixture("test.py");
        let actual = policies.eval(&fixture_operation);
        let expected = true;
        assert_eq!(actual, expected);

        let fixture_operation = create_write_operation_fixture("test.js");
        let actual = policies.eval(&fixture_operation);
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_policy_not_logic() {
        let fixture_policy = !Policy::new(
            Permission::DisallowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test.rs");
        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_find_rules_single_match() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test.rs");

        let actual = fixture_policy.find_rules(&fixture_operation);
        let expected = vec![Rule::Write { pattern: Pattern::new("*.rs").unwrap() }];

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_find_rules_no_match() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test.py");

        let actual = fixture_policy.find_rules(&fixture_operation);
        let expected: Vec<Rule> = vec![];

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_glob_matches_wildcard() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("any/path/file.txt");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_glob_matches_prefix() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("test*").unwrap() },
        );
        let fixture_operation = create_write_operation_fixture("test_file.rs");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_read_operation() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Read { pattern: Pattern::new("*.md").unwrap() },
        );
        let fixture_operation = create_read_operation_fixture("README.md");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_execute_operation() {
        let fixture_policy = Policy::new(
            Permission::AllowAlways,
            Rule::Execute { command: Pattern::new("cargo*").unwrap() },
        );
        let fixture_operation = create_execute_operation_fixture("cargo build");

        let actual = fixture_policy.eval(&fixture_operation);
        let expected = true;

        assert_eq!(actual, expected);
    }
}
