// Measures impact of context compaction by comparing two contexts
//
// This module provides a function to calculate the improvement between
// two Context instances, helping evaluate the effectiveness of compaction
// strategies.

use crate::Context;

pub fn calculate_compaction_improvement(original: &Context, new: &Context) -> f64 {
    // Get textual representation of both contexts
    let original_text = original.to_text();
    let new_text = new.to_text();

    // If both contexts are identical
    if original_text == new_text {
        return 0.0;
    }

    // Get the lengths
    let original_length = original_text.len();
    let new_length = new_text.len();

    // Edge cases
    if original_length == 0 {
        // If original was empty but new is not, this is a regression
        if new_length > 0 {
            return -100.0;
        }
        return 0.0; // Both empty
    }

    // Calculate percentage change in length
    // Positive percentage means the new context is smaller (improvement)
    // Negative percentage means the new context is larger (regression)
    ((original_length as f64 - new_length as f64) / original_length as f64) * 100.0
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::ContextMessage;

    #[test]
    fn test_improvement_with_smaller_context() {
        // Create a fixture with original and compacted contexts
        let original = Context::default()
            .add_message(ContextMessage::user("First message"))
            .add_message(ContextMessage::user("Second message"))
            .add_message(ContextMessage::user("Third message"));

        let compacted =
            Context::default().add_message(ContextMessage::user("Summary of three messages"));

        let actual = calculate_compaction_improvement(&original, &compacted);

        // The compacted version should be smaller, resulting in positive improvement
        assert!(actual > 0.0);
    }

    #[test]
    fn test_improvement_with_larger_context() {
        // Create a fixture where the "compacted" context is actually larger
        let original = Context::default().add_message(ContextMessage::user("Short message"));

        let expanded = Context::default().add_message(ContextMessage::user(
            "This is a much longer message that contains more text than the original",
        ));

        let actual = calculate_compaction_improvement(&original, &expanded);

        // The expanded version should be larger, resulting in negative improvement
        assert!(actual < 0.0);
    }

    #[test]
    fn test_improvement_with_identical_contexts() {
        // Create identical contexts
        let context1 = Context::default().add_message(ContextMessage::user("Same message"));

        let context2 = Context::default().add_message(ContextMessage::user("Same message"));

        let actual = calculate_compaction_improvement(&context1, &context2);

        // Identical contexts should have zero improvement
        assert_eq!(actual, 0.0);
    }

    #[test]
    fn test_improvement_with_empty_contexts() {
        // Empty contexts
        let empty1 = Context::default();
        let empty2 = Context::default();

        let actual = calculate_compaction_improvement(&empty1, &empty2);

        // Empty contexts should have zero improvement
        assert_eq!(actual, 0.0);
    }

    #[test]
    fn test_improvement_empty_to_nonempty() {
        // From empty to non-empty (regression)
        let empty = Context::default();
        let nonempty = Context::default().add_message(ContextMessage::user("New content"));

        let actual = calculate_compaction_improvement(&empty, &nonempty);

        // Going from empty to non-empty is a regression
        assert!(actual < 0.0);
    }
}
