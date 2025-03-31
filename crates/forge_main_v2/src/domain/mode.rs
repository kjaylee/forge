use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub struct ForgeMode(String);

impl ForgeMode {
    pub fn new(value: impl ToString) -> Self {
        Self(value.to_string().to_uppercase())
    }

    pub fn value(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ForgeMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// PartialEq implementations for string comparisons
impl PartialEq<str> for ForgeMode {
    fn eq(&self, other: &str) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

impl PartialEq<&str> for ForgeMode {
    fn eq(&self, other: &&str) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

impl PartialEq<String> for ForgeMode {
    fn eq(&self, other: &String) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_forge_mode_creation() {
        let fixture = ForgeMode::new("ACT");
        let expected = "ACT";

        assert_eq!(fixture.value(), expected);
        assert_eq!(fixture, "act");
        assert_eq!(fixture, "ACT");
        assert_eq!(fixture, String::from("act"));
    }

    #[test]
    fn test_forge_mode_display() {
        let fixture = ForgeMode::new("plan");
        let actual = fixture.to_string();
        let expected = "PLAN";

        assert_eq!(actual, expected);
    }
}
