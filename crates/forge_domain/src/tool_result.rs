use std::fmt::Display;

use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{ToolCallFull, ToolCallId, ToolName};

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
pub struct ToolResult {
    pub name: ToolName,
    pub call_id: Option<ToolCallId>,
    #[setters(skip)]
    pub content: String,
    #[setters(skip)]
    pub is_error: bool,
}

#[derive(Default, Serialize, Setters)]
#[serde(rename_all = "snake_case", rename = "tool_result")]
#[setters(strip_option)]
struct ToolResultXML {
    tool_name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    success: Option<String>,
}

impl ToolResult {
    pub fn new(name: ToolName) -> ToolResult {
        Self {
            name,
            call_id: None,
            content: String::default(),
            is_error: false,
        }
    }

    pub fn success(mut self, content: Value) -> Self {
        self.content = match content {
            Value::String(s) => s,
            _ => content.to_string(),
        };
        self.is_error = false;
        self
    }

    pub fn failure(mut self, content: impl Into<String>) -> Self {
        self.content = content.into();
        self.is_error = true;
        self
    }
}

impl From<ToolCallFull> for ToolResult {
    fn from(value: ToolCallFull) -> Self {
        Self {
            name: value.name,
            call_id: value.call_id,
            content: String::default(),
            is_error: false,
        }
    }
}

impl Display for ToolResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let xml = {
            let xml = ToolResultXML::default().tool_name(self.name.as_str().to_owned());
            if self.is_error {
                xml.error(self.content.clone())
            } else {
                xml.success(self.content.clone())
            }
        };

        // First serialize to string
        let mut out = String::new();
        let ser = quick_xml::se::Serializer::new(&mut out);
        xml.serialize(ser).unwrap();

        write!(f, "{}", out)
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    use serde_json::json;

    use super::*;

    fn assert_xml_eq(actual: impl Display, expected: impl Display) {
        pretty_assertions::assert_eq!(actual.to_string(), expected.to_string());
    }

    fn xml(name: &str, content: Option<(&str, &str)>) -> String {
        match content {
            Some((tag, value)) => format!(
                "<tool_result>\
                    <tool_name>{name}</tool_name>\
                    <{tag}>{value}</{tag}>\
                </tool_result>"
            ),
            None => format!(
                "<tool_result>\
                    <tool_name>{name}</tool_name>\
                    <success/>\
                </tool_result>"
            ),
        }
    }

    #[test]
    fn test_minimal() {
        let result = ToolResult::new(ToolName::new("test_tool"));
        assert_xml_eq(result, xml("test_tool", None));
    }

    #[test]
    fn test_full() {
        let result = ToolResult::new(ToolName::new("complex_tool"))
            .call_id(ToolCallId::new("123"))
            .failure(json!({"key": "value", "number": 42}).to_string());

        let expected = xml(
            "complex_tool",
            Some(("error", "{\"key\":\"value\",\"number\":42}")),
        );

        assert_xml_eq(result, expected);
    }

    #[test]
    fn test_with_special_chars() {
        let result = ToolResult::new(ToolName::new("xml_tool")).success(json!({
            "text": "Special chars: < > & ' \"",
            "nested": {
                "html": "<div>Test</div>"
            }
        }));

        let expected = xml(
            "xml_tool",
            Some((
                "success",
                "{\"nested\":{\"html\":\"&lt;div&gt;Test&lt;/div&gt;\"},\
             \"text\":\"Special chars: &lt; &gt; &amp; ' \\\"\"}",
            )),
        );

        assert_xml_eq(result, expected);
    }

    #[test]
    fn test_display_with_complex_json() {
        let result = ToolResult::new(ToolName::new("complex_tool"))
            .call_id(ToolCallId::new("123"))
            .success(json!({
                "user": "John Doe",
                "age": 42,
                "address": [{"city": "New York"}, {"city": "Los Angeles"}]
            }));

        let expected = xml(
            "complex_tool",
            Some((
                "success",
                "{\"address\":[{\"city\":\"New York\"},{\"city\":\"Los Angeles\"}],\
              \"age\":42,\"user\":\"John Doe\"}",
            )),
        );

        assert_xml_eq(result, expected);
    }

    #[test]
    fn test_display_special_chars() {
        let result = ToolResult::new(ToolName::new("xml_tool")).success(json!({
            "text": "Special chars: < > & ' \"",
            "nested": {
                "html": "<div>Test</div>"
            }
        }));

        let expected = xml(
            "xml_tool",
            Some((
                "success",
                "{\"nested\":{\"html\":\"&lt;div&gt;Test&lt;/div&gt;\"},\
              \"text\":\"Special chars: &lt; &gt; &amp; ' \\\"\"}",
            )),
        );

        assert_xml_eq(result, expected);
    }

    #[test]
    fn test_success_and_failure_content() {
        let success = ToolResult::new(ToolName::new("test_tool")).success(json!("success message"));
        assert!(!success.is_error);
        assert_eq!(success.content, "success message");

        let failure = ToolResult::new(ToolName::new("test_tool")).failure("error message");
        assert!(failure.is_error);
        assert_eq!(failure.content, "error message");
    }
}
