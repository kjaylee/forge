/// Formats an issue revise-plan command input from comment for consumption by
/// revise_plan event
///
/// # Arguments
///
/// * `issue_number` - The issue number
/// * `comment_body` - The entire comment body containing the revise-plan
///   command and feedback
///
/// # Returns
///
/// A string in the format "issue_number|feedback" where feedback is the content
/// after the command
pub fn format_revise_plan_input(issue_number: u32, comment_body: &str) -> String {
    let command = "/forge revise-plan";
    let feedback = comment_body.trim_start_matches(command).trim();
    format!("{}|{}", issue_number, feedback)
}

#[cfg(test)]
mod tests {
    use crate::format_revise_plan_input;

    #[test]
    fn test_format_revise_plan_input() {
        // Test with simple feedback
        let result = format_revise_plan_input(123, "/forge revise-plan Please add more tests");
        assert_eq!(result, "123|Please add more tests");

        // Test with multiline feedback
        let result = format_revise_plan_input(
            456,
            "/forge revise-plan Please consider the following:\n1. More tests\n2. Better docs\n3. Refactor code"
        );
        assert_eq!(
            result,
            "456|Please consider the following:\n1. More tests\n2. Better docs\n3. Refactor code"
        );

        // Test with no feedback
        let result = format_revise_plan_input(789, "/forge revise-plan");
        assert_eq!(result, "789|");

        // Test with whitespace at end of command
        let result = format_revise_plan_input(123, "/forge revise-plan   Feedback with spaces");
        assert_eq!(result, "123|Feedback with spaces");
    }
}
