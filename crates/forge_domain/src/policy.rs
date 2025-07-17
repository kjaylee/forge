use std::fmt::Display;
use std::ops::DerefMut;
use std::path::PathBuf;
use std::{collections::VecDeque, ops::Deref};

use derive_setters::Setters;
use glob::Pattern as GlobPattern;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::Tools;

/// Serializable wrapper around glob::Pattern
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern(GlobPattern);

impl Pattern {
    /// Create a new Pattern from a string
    pub fn new(pattern: &str) -> Result<Self, glob::PatternError> {
        let glob_pattern = GlobPattern::new(pattern)?;
        Ok(Pattern(glob_pattern))
    }
}

impl Deref for Pattern {
    type Target = GlobPattern;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Pattern {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Serialize for Pattern {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.as_str().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Pattern {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let pattern_str = String::deserialize(deserializer)?;
        Pattern::new(&pattern_str).map_err(serde::de::Error::custom)
    }
}

/// Represents different permission levels for policy evaluation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, JsonSchema, Eq)]
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
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub enum Rule {
    /// File write operations with glob pattern matching
    Write { pattern: Pattern },
    /// File read operations with glob pattern matching
    Read { pattern: Pattern },
    /// Command execution with glob pattern matching
    Execute { command: Pattern },
}

/// Represents a policy that can be evaluated against operations
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub enum Policy {
    /// A simple policy with permission and rule
    Policy { permission: Permission, rule: Rule },
    /// Logical AND of two policies
    And(Box<Policy>, Box<Policy>),
    /// Logical OR of two policies
    Or(Box<Policy>, Box<Policy>),
}

/// Represents an operation that needs policy evaluation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, JsonSchema, Eq)]
pub enum Operation {
    /// File write operation
    Write { path: PathBuf },
    /// File read operation
    Read { path: PathBuf },
    /// Command execution
    Execute { command: String },
}

impl Operation {
    pub fn write(path: PathBuf) -> Self {
        Operation::Write { path }
    }

    pub fn read(path: PathBuf) -> Self {
        Operation::Read { path }
    }

    pub fn execute(command: String) -> Self {
        Operation::Execute { command }
    }
}

impl From<&Tools> for Option<Operation> {
    fn from(value: &Tools) -> Self {
        match value {
            Tools::ForgeToolFsRead(input) => Some(Operation::read(PathBuf::from(&input.path))),
            Tools::ForgeToolFsCreate(input) => Some(Operation::write(PathBuf::from(&input.path))),
            Tools::ForgeToolFsPatch(input) => Some(Operation::write(PathBuf::from(&input.path))),
            Tools::ForgeToolFsRemove(input) => Some(Operation::write(PathBuf::from(&input.path))),
            Tools::ForgeToolProcessShell(input) => Some(Operation::execute(input.command.clone())),
            Tools::ForgeToolFsSearch(input) => Some(Operation::read(PathBuf::from(&input.path))),
            _ => None,
        }
    }
}

/// Result of policy evaluation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyStatus {
    /// Operation is allowed
    Pass,
    /// Operation is denied
    Fail,
}

impl Display for PolicyStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolicyStatus::Pass => write!(f, "Policy evaluation passed"),
            PolicyStatus::Fail => write!(f, "Policy evaluation failed"),
        }
    }
}

/// Represents a policy evaluation result with the policy and its outcome
#[derive(Debug, Clone, PartialEq, Setters)]
pub struct PolicyTrace {
    pub policy: Policy,
    pub status: PolicyStatus,
    pub reason: Option<String>,
}

impl PolicyTrace {
    /// Create a new evaluation result
    pub fn new(policy: Policy, status: PolicyStatus) -> Self {
        PolicyTrace { policy, status, reason: None }
    }

    /// Check if the evaluation passed
    pub fn is_pass(&self) -> bool {
        self.status == PolicyStatus::Pass
    }

    /// Check if the evaluation failed
    pub fn is_fail(&self) -> bool {
        self.status == PolicyStatus::Fail
    }

    /// Check if this is a compound policy that should show sub-policies
    /// indented
    pub fn is_compound_policy(&self) -> bool {
        !self.policy.is_policy()
    }
}

impl std::fmt::Display for PolicyTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // All policies get the same formatting - the indentation is handled by PolicyValidation
        write!(f, "{}", self.policy)?;
        write!(f, " {}", self.status)?;
        if let Some(reason) = &self.reason {
            write!(f, " ({reason})")?;
        }
        Ok(())
    }
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

/// Represents a trace entry for policy evaluation with error context
#[derive(Clone, PartialEq, Debug, Setters, Error)]
pub struct Trace<E, T> {
    pub error: E,
    #[setters(skip)]
    pub trace: VecDeque<T>,
}

impl<E, T> Trace<E, T> {
    pub fn new(error: E) -> Self {
        Trace { error, trace: Default::default() }
    }

    pub fn trace(mut self, context: T) -> Self {
        self.trace.push_front(context);
        self
    }

    pub fn transform<E1>(self, f: impl Fn(E) -> E1) -> Trace<E1, T> {
        Trace { error: f(self.error), trace: self.trace }
    }
}

/// A validation type for policy evaluation that can accumulate errors with
/// trace context
#[derive(Debug, PartialEq)]
pub struct Valid<A, E, T>(Result<A, Vec<Trace<E, T>>>);

impl<A, E, T> Valid<A, E, T> {
    /// Creates a successful validation
    pub fn succeed(value: A) -> Self {
        Valid(Ok(value))
    }

    /// Creates a failed validation with a single error
    pub fn fail(error: E) -> Self {
        Valid(Err(vec![Trace::new(error)]))
    }

    /// Creates a failed validation with error and trace context
    pub fn fail_at(error: E, trace: T) -> Self {
        Valid(Err(vec![Trace::new(error).trace(trace)]))
    }

    /// Returns true if validation succeeded
    pub fn is_succeed(&self) -> bool {
        self.0.is_ok()
    }

    /// Returns true if validation failed
    pub fn is_fail(&self) -> bool {
        self.0.is_err()
    }

    /// Returns the successful value if validation succeeded
    pub fn value(self) -> Option<A> {
        self.0.ok()
    }

    /// Maps a function over the successful value
    pub fn map<B>(self, f: impl FnOnce(A) -> B) -> Valid<B, E, T> {
        Valid(self.0.map(f))
    }

    /// Adds trace context to any errors in the validation
    pub fn trace(self, context: impl Into<T> + Clone) -> Valid<A, E, T> {
        match self.0 {
            Ok(value) => Valid(Ok(value)),
            Err(errors) => Valid(Err(errors
                .into_iter()
                .map(|trace| trace.trace(context.clone().into()))
                .collect())),
        }
    }

    /// Combines two validations with logical AND
    pub fn and<B>(self, other: Valid<B, E, T>) -> Valid<B, E, T> {
        match (self.0, other.0) {
            (Ok(_), Ok(b)) => Valid(Ok(b)),
            (Err(e1), Ok(_)) => Valid(Err(e1)),
            (Ok(_), Err(e2)) => Valid(Err(e2)),
            (Err(mut e1), Err(e2)) => {
                e1.extend(e2);
                Valid(Err(e1))
            }
        }
    }

    /// Combines two validations with logical OR
    pub fn or(self, other: Valid<A, E, T>) -> Valid<A, E, T> {
        match (self.0, other.0) {
            (Ok(a), _) => Valid(Ok(a)),
            (_, Ok(a)) => Valid(Ok(a)),
            (Err(mut e1), Err(e2)) => {
                e1.extend(e2);
                Valid(Err(e1))
            }
        }
    }

    /// Converts to Result
    pub fn to_result(self) -> Result<A, Vec<Trace<E, T>>> {
        self.0
    }

    /// Gets the errors if validation failed
    pub fn errors(&self) -> Option<&Vec<Trace<E, T>>> {
        self.0.as_ref().err()
    }
}

impl<A, E, T> From<Trace<E, T>> for Valid<A, E, T> {
    fn from(trace: Trace<E, T>) -> Self {
        Valid(Err(vec![trace]))
    }
}

impl<A, E, T> From<Vec<Trace<E, T>>> for Valid<A, E, T> {
    fn from(traces: Vec<Trace<E, T>>) -> Self {
        Valid(Err(traces))
    }
}

impl<A: Display, E: Display, T: Display> Display for Valid<A, E, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Ok(value) => write!(f, "✓ {value}"),
            Err(traces) => {
                writeln!(f, "✗ Policy validation failed:")?;
                for (i, trace) in traces.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    Self::write_trace_hierarchical(f, trace, 2)?;
                }
                Ok(())
            }
        }
    }
}

impl<A, E: Display, T: Display> Valid<A, E, T> {
    fn write_trace_hierarchical(
        f: &mut std::fmt::Formatter<'_>,
        trace: &Trace<E, T>,
        base_indent: usize,
    ) -> std::fmt::Result {
        // Write trace entries with proper depth-based indentation
        for (depth, entry) in trace.trace.iter().enumerate() {
            let indent = base_indent + (depth * 2);
            let indent_str = " ".repeat(indent);
            writeln!(f, "{indent_str}{entry}")?;
        }
        Ok(())
    }
}

pub type PolicyResult<T> = std::result::Result<T, PolicyError>;

pub enum EvalResult {
    Allow,
    Deny(Policy),
    Confirm(Policy),
}

impl Display for EvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalResult::Allow => write!(f, "Allowed"),
            EvalResult::Deny(policy) => write!(f, "Denied because of policy: {}", policy),
            EvalResult::Confirm(policy) => write!(
                f,
                "Confirm operation is required because of policy: {}",
                policy
            ),
        }
    }
}

impl Policy {
    /// Create a new simple policy
    pub fn new(permission: Permission, rule: Rule) -> Self {
        Policy::Policy { permission, rule }
    }

    /// Checks if it's standard policy
    pub fn is_policy(&self) -> bool {
        matches!(self, Policy::Policy { .. })
    }

    /// Combine two policies with logical AND
    pub fn and(self, other: Policy) -> Self {
        Policy::And(Box::new(self), Box::new(other))
    }

    /// Combine two policies with logical OR
    pub fn or(self, other: Policy) -> Self {
        Policy::Or(Box::new(self), Box::new(other))
    }

    /// Checks if for a operation if rule exists
    fn rule_exists(&self, operation: &Operation) -> bool {
        match self {
            Policy::Policy { rule, .. } => self.is_rule_defined(rule, operation),
            Policy::And(left, right) => left.rule_exists(operation) && right.rule_exists(operation),
            Policy::Or(left, right) => left.rule_exists(operation) || right.rule_exists(operation),
        }
    }

    /// Evaluate the policy against an operation with detailed trace information
    pub fn eval(&self, operation: &Operation) -> Valid<EvalResult, String, PolicyTrace> {
        if !self.rule_exists(operation) {
            // Since rule is not defined for this operation, we reverts to default policy.
            return Valid::succeed(EvalResult::Confirm(self.clone()));
        }

        match self {
            Policy::Policy { permission, rule } => {
                if self.evaluate_rule(rule, operation) {
                    // TODO: need a state check if the permission is already granted
                    // or denied once
                    // For now, we assume the permission is valid
                    // and return it directly
                    match permission {
                        Permission::AllowOnce => Valid::succeed(EvalResult::Allow),
                        Permission::DisallowOnce => Valid::succeed(EvalResult::Deny(self.clone())),
                        Permission::AllowAlways => Valid::succeed(EvalResult::Allow),
                        Permission::DisallowAlways => {
                            Valid::succeed(EvalResult::Deny(self.clone()))
                        }
                        Permission::Confirm => Valid::succeed(EvalResult::Confirm(self.clone())),
                    }
                } else {
                    // rule evaluation failed for this operation
                    Valid::fail("Rule evaluation failed for this operation.".to_string()).trace(
                        PolicyTrace::new(self.clone(), PolicyStatus::Fail).reason(Some(
                            "Rule evaluation failed for this operation.".to_string(),
                        )),
                    )
                }
            }
            Policy::And(left, right) => {
                let left_result = left.eval(operation);
                let right_result = right.eval(operation);
                let result = left_result.and(right_result);
                if result.is_succeed() {
                    result
                } else {
                    result.trace(PolicyTrace::new(self.clone(), PolicyStatus::Fail))
                }
            }
            Policy::Or(left, right) => {
                let left_result = left.eval(operation);
                let right_result = right.eval(operation);

                let result = left_result.or(right_result);
                if result.is_succeed() {
                    result
                } else {
                    result.trace(PolicyTrace::new(self.clone(), PolicyStatus::Fail))
                }
            }
        }
    }
}

impl Policy {
    /// check is rule is defined for the operation
    fn is_rule_defined(&self, rule: &Rule, operation: &Operation) -> bool {
        match (rule, operation) {
            (Rule::Write { pattern: _ }, Operation::Write { path: _ }) => true,
            (Rule::Read { pattern: _ }, Operation::Read { path: _ }) => true,
            (Rule::Execute { command: _ }, Operation::Execute { command: _ }) => true,
            _ => false,
        }
    }

    /// Check if a rule matches an operation
    fn evaluate_rule(&self, rule: &Rule, operation: &Operation) -> bool {
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
}

impl Display for Permission {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Permission::AllowOnce => write!(f, "AllowOnce"),
            Permission::DisallowOnce => write!(f, "DisallowOnce"),
            Permission::AllowAlways => write!(f, "AllowAlways"),
            Permission::DisallowAlways => write!(f, "DisallowAlways"),
            Permission::Confirm => write!(f, "Confirm"),
        }
    }
}

impl Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::Write { pattern } => write!(f, "Write({})", pattern.as_str()),
            Rule::Read { pattern } => write!(f, "Read({})", pattern.as_str()),
            Rule::Execute { command } => write!(f, "Execute({})", command.as_str()),
        }
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Write { path } => write!(f, "Write({})", path.display()),
            Operation::Read { path } => write!(f, "Read({})", path.display()),
            Operation::Execute { command } => write!(f, "Execute({command})"),
        }
    }
}

impl Display for Policy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Policy::Policy { permission, rule } => {
                write!(f, "Policy({permission}, {rule})")
            }
            Policy::And(left, right) => {
                write!(f, "AND({left}, {right})")
            }
            Policy::Or(left, right) => {
                write!(f, "OR({left}, {right})")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn create_write_operation_fixture(path: &str) -> Operation {
        Operation::Write { path: PathBuf::from(path) }
    }

    fn create_read_operation_fixture(path: &str) -> Operation {
        Operation::Read { path: PathBuf::from(path) }
    }

    fn create_execute_operation_fixture(command: &str) -> Operation {
        Operation::Execute { command: command.to_string() }
    }

    /// Test hierarchical indentation with nested compound policies
    #[test]
    fn test_hierarchical_indentation() {
        let policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("*.rs").unwrap() },
        )
        .or(Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("src/*").unwrap() },
        ))
        .or(Policy::new(
            Permission::DisallowAlways,
            Rule::Write { pattern: Pattern::new("*").unwrap() },
        ));
        let fixture_operation = create_write_operation_fixture("test.rs");
        let actual = policy.eval(&fixture_operation);

        assert!(actual.is_succeed());
    }

    /// Test allowing command execution in current working directory
    #[test]
    fn test_allow_only_cargo_command_execution() {
        let fixture = Policy::new(
            Permission::AllowAlways,
            Rule::Execute { command: Pattern::new("cargo*").unwrap() },
        );
        let actual = fixture.eval(&create_execute_operation_fixture("cargo build"));
        assert!(actual.is_succeed());
        let actual = fixture.eval(&create_execute_operation_fixture("ls -la"));
        assert!(actual.is_fail());
    }

    #[test]
    fn test_allow_user_to_modify_forge_file() {
        // allow user to r/w forge.toml
        let policy = Policy::new(
            Permission::AllowAlways,
            Rule::Write { pattern: Pattern::new("forge.yaml").unwrap() },
        )
        .or(Policy::new(
            Permission::AllowAlways,
            Rule::Read { pattern: Pattern::new("forge.yaml").unwrap() },
        ));

        let fixture_operation = create_write_operation_fixture("forge.yaml");
        let actual = policy.eval(&fixture_operation);
        assert!(actual.is_succeed());

        let fixture_operation = create_read_operation_fixture("forge.yaml");
        let actual = policy.eval(&fixture_operation);
        assert!(actual.is_succeed());

        let fixture_operation = create_read_operation_fixture("forge.default.yaml");
        let actual = policy.eval(&fixture_operation);
        assert!(actual.is_fail());
    }
}
