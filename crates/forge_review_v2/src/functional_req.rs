use std::fmt::Display;
use pulldown_cmark::{Parser, Event, Tag, HeadingLevel};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionalRequirements {
    pub title: String,
    pub overview: String,
    pub requirements: Vec<Requirement>,
    pub dependencies: Vec<Dependency>,
    pub ambiguities: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Requirement {
    pub id: String,        // e.g. "R1"
    pub name: String,      // e.g. "Task Completion Command"
    pub statement: String, // The "shall" statement
    pub acceptance_criteria: Vec<String>,
}

impl Display for Requirement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "id: {}", self.id)?;
        writeln!(f, "name: {}", self.name)?;
        writeln!(f, "statement: {}", self.statement)?;
        writeln!(
            f,
            "acceptance_criteria: {}",
            self.acceptance_criteria.join(", ")
        )?;
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dependency {
    pub id: String,       // e.g. "D1"
    pub from_req: String, // e.g. "R3"
    pub to_req: String,   // e.g. "R2"
    pub explanation: String,
}

#[derive(Debug)]
enum ParsingState {
    Initial,
    Overview,
    Requirements,
    Dependencies,
    Ambiguities,
}

#[derive(Debug)]
enum RequirementParsingState {
    Initial,
    Statement,
    AcceptanceCriteria,
}

impl FunctionalRequirements {
    pub fn parse(content: &str) -> Result<Self, String> {
        let parser = Parser::new(content);
        let mut state = ParsingState::Initial;
        let mut req_state = RequirementParsingState::Initial;
        
        let mut title = String::new();
        let mut overview = String::new();
        let mut requirements = Vec::new();
        let mut dependencies = Vec::new();
        let mut ambiguities = Vec::new();
        
        // Current requirement being parsed
        let mut current_req = Requirement {
            id: String::new(),
            name: String::new(),
            statement: String::new(),
            acceptance_criteria: Vec::new(),
        };
        
        // Current dependency being parsed
        let mut current_dep = Dependency {
            id: String::new(),
            from_req: String::new(),
            to_req: String::new(),
            explanation: String::new(),
        };
        
        let mut current_text = String::new();
        let mut in_strong = false;
        
        for event in parser {
            match event {
                Event::Start(Tag::Heading(level, ..)) => {
                    current_text.clear();
                    match level {
                        HeadingLevel::H1 => state = ParsingState::Initial,
                        HeadingLevel::H2 => {
                            // Save current requirement if any
                            if !current_req.id.is_empty() {
                                requirements.push(current_req.clone());
                                current_req = Requirement {
                                    id: String::new(),
                                    name: String::new(),
                                    statement: String::new(),
                                    acceptance_criteria: Vec::new(),
                                };
                            }
                        }
                        HeadingLevel::H3 => {
                            if matches!(state, ParsingState::Requirements) {
                                // Save current requirement if any
                                if !current_req.id.is_empty() {
                                    requirements.push(current_req.clone());
                                }
                                current_req = Requirement {
                                    id: String::new(),
                                    name: String::new(),
                                    statement: String::new(),
                                    acceptance_criteria: Vec::new(),
                                };
                                req_state = RequirementParsingState::Initial;
                            }
                        }
                        _ => {}
                    }
                }
                Event::End(Tag::Heading(level, ..)) => {
                    let text = current_text.trim();
                    match level {
                        HeadingLevel::H1 => {
                            if text.starts_with("Functional Requirements:") {
                                title = text.trim_start_matches("Functional Requirements:").trim().to_string();
                            }
                        }
                        HeadingLevel::H2 => {
                            match text {
                                "Overview" => state = ParsingState::Overview,
                                "Functional Requirements" => state = ParsingState::Requirements,
                                "Dependencies" => state = ParsingState::Dependencies,
                                "Notes on Ambiguities" => state = ParsingState::Ambiguities,
                                _ => {}
                            }
                        }
                        HeadingLevel::H3 => {
                            if matches!(state, ParsingState::Requirements) {
                                let parts: Vec<&str> = text.split(':').collect();
                                if parts.len() == 2 {
                                    current_req.id = parts[0].trim().to_string();
                                    current_req.name = parts[1].trim().to_string();
                                }
                            }
                        }
                        _ => {}
                    }
                    current_text.clear();
                }
                Event::Start(Tag::Strong) => {
                    in_strong = true;
                    current_text.clear();
                }
                Event::End(Tag::Strong) => {
                    let text = current_text.trim();
                    match text {
                        "Requirement:" => req_state = RequirementParsingState::Statement,
                        "Acceptance Criteria:" => req_state = RequirementParsingState::AcceptanceCriteria,
                        _ if text.ends_with(':') && matches!(state, ParsingState::Dependencies) => {
                            current_dep.id = text.trim_end_matches(':').to_string();
                        }
                        _ => {}
                    }
                    in_strong = false;
                    current_text.clear();
                }
                Event::Start(Tag::List(_)) => {}
                Event::End(Tag::List(_)) => {}
                Event::Start(Tag::Item) => {
                    current_text.clear();
                }
                Event::End(Tag::Item) => {
                    let text = current_text.trim();
                    match state {
                        ParsingState::Requirements => {
                            match req_state {
                                RequirementParsingState::Statement => {
                                    if !in_strong {
                                        current_req.statement = text.to_string();
                                    }
                                }
                                RequirementParsingState::AcceptanceCriteria => {
                                    if !text.is_empty() {
                                        current_req.acceptance_criteria.push(text.to_string());
                                    }
                                }
                                _ => {}
                            }
                        }
                        ParsingState::Dependencies => {
                            if !current_dep.id.is_empty() {
                                if let Some((reqs, explanation)) = text.split_once('[') {
                                    if let Some((from, to)) = reqs.split_once("depends on") {
                                        current_dep.from_req = from.trim().to_string();
                                        current_dep.to_req = to.trim().to_string();
                                        current_dep.explanation = explanation.trim_end_matches(']').trim().to_string();
                                        dependencies.push(current_dep.clone());
                                        current_dep = Dependency {
                                            id: String::new(),
                                            from_req: String::new(),
                                            to_req: String::new(),
                                            explanation: String::new(),
                                        };
                                    }
                                }
                            }
                        }
                        ParsingState::Ambiguities => {
                            if !text.is_empty() {
                                ambiguities.push(text.to_string());
                            }
                        }
                        _ => {}
                    }
                    current_text.clear();
                }
                Event::Text(text) => {
                    current_text.push_str(text.as_ref());
                }
                Event::Start(Tag::Paragraph) => {
                    current_text.clear();
                }
                Event::End(Tag::Paragraph) => {
                    let text = current_text.trim();
                    if matches!(state, ParsingState::Overview) && !text.is_empty() {
                        overview = text.to_string();
                    }
                    current_text.clear();
                }
                _ => {}
            }
        }
        
        // Add the last requirement if any
        if !current_req.id.is_empty() {
            requirements.push(current_req);
        }
        
        if title.is_empty() {
            return Err("Missing title".to_string());
        }
        
        Ok(FunctionalRequirements {
            title,
            overview,
            requirements,
            dependencies,
            ambiguities,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_functional_requirements() {
        let content = r#"# Functional Requirements: Test Feature

## Overview
This is a test overview.

## Functional Requirements

### R1: First Requirement
- **Requirement:** The system shall do something.
- **Acceptance Criteria:**
  - Criterion 1
  - Criterion 2

### R2: Second Requirement
- **Requirement:** The system shall do something else.
- **Acceptance Criteria:**
  - Criterion 3
  - Criterion 4

## Dependencies

- **D1:** R2 depends on R1 [needs first thing to work]

## Notes on Ambiguities
- First ambiguity note
- Second ambiguity note"#;

        let result = FunctionalRequirements::parse(content).unwrap();
        assert_eq!(result.title, "Test Feature");
        assert_eq!(result.overview, "This is a test overview.");
        assert_eq!(result.requirements.len(), 2);
        assert_eq!(result.dependencies.len(), 1);
        assert_eq!(result.ambiguities.len(), 2);
        
        // Test first requirement
        let r1 = &result.requirements[0];
        assert_eq!(r1.id, "R1");
        assert_eq!(r1.name, "First Requirement");
        assert_eq!(r1.statement, "The system shall do something.");
        assert_eq!(r1.acceptance_criteria, vec!["Criterion 1", "Criterion 2"]);
        
        // Test second requirement
        let r2 = &result.requirements[1];
        assert_eq!(r2.id, "R2");
        assert_eq!(r2.name, "Second Requirement");
        assert_eq!(r2.statement, "The system shall do something else.");
        assert_eq!(r2.acceptance_criteria, vec!["Criterion 3", "Criterion 4"]);
        
        // Test dependency
        let d1 = &result.dependencies[0];
        assert_eq!(d1.id, "D1");
        assert_eq!(d1.from_req, "R2");
        assert_eq!(d1.to_req, "R1");
        assert_eq!(d1.explanation, "needs first thing to work");
        
        // Test ambiguities
        assert_eq!(result.ambiguities[0], "First ambiguity note");
        assert_eq!(result.ambiguities[1], "Second ambiguity note");
    }
    
    #[test]
    fn test_parse_empty_content() {
        let result = FunctionalRequirements::parse("");
        assert!(result.is_err());
    }
    
    #[test]
    fn test_parse_missing_sections() {
        let content = r#"# Functional Requirements: Test Feature

## Overview
This is a test overview.
"#;
        let result = FunctionalRequirements::parse(content).unwrap();
        assert_eq!(result.title, "Test Feature");
        assert_eq!(result.overview, "This is a test overview.");
        assert!(result.requirements.is_empty());
        assert!(result.dependencies.is_empty());
        assert!(result.ambiguities.is_empty());
    }
}
