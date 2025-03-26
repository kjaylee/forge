use std::fmt::Display;

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

impl FunctionalRequirements {
    pub fn parse(content: &str) -> Result<Self, String> {
        let sections: Vec<&str> = content.split("\n## ").collect();
        if sections.is_empty() {
            return Err("Empty content".to_string());
        }

        // Parse header and overview
        let header = sections[0].trim();
        let title = header
            .lines()
            .next()
            .ok_or("Missing title")?
            .trim_start_matches("# ")
            .trim_start_matches("Functional Requirements: ")
            .to_string();

        let overview = header
            .lines()
            .skip_while(|l| !l.contains("Overview"))
            .skip(1)
            .take_while(|l| !l.is_empty())
            .collect::<Vec<_>>()
            .join("\n")
            .trim()
            .to_string();

        // Parse requirements
        let requirements_section = sections
            .iter()
            .find(|s| s.trim().starts_with("Functional Requirements"))
            .ok_or("Missing Functional Requirements section")?;

        let mut requirements = Vec::new();
        for req_block in requirements_section.split("\n### ").skip(1) {
            let mut lines = req_block.lines();
            let header = lines.next().ok_or("Missing requirement header")?;
            let id = header
                .split(':')
                .next()
                .ok_or("Invalid requirement format")?
                .trim()
                .to_string();
            let name = header
                .split(':')
                .nth(1)
                .ok_or("Missing requirement name")?
                .trim()
                .to_string();

            let mut statement = String::new();
            let mut criteria = Vec::new();
            let mut in_criteria = false;

            for line in lines {
                if line.contains("**Requirement:**") {
                    statement = line
                        .split("**Requirement:**")
                        .nth(1)
                        .unwrap_or("")
                        .trim()
                        .to_string();
                } else if line.contains("**Acceptance Criteria:**") {
                    in_criteria = true;
                } else if in_criteria && line.trim().starts_with('-') {
                    criteria.push(line.trim_start_matches('-').trim().to_string());
                }
            }

            requirements.push(Requirement { id, name, statement, acceptance_criteria: criteria });
        }

        // Parse dependencies
        let dependencies_section = sections
            .iter()
            .find(|s| s.trim().starts_with("Dependencies")).copied()
            .unwrap_or("");

        let mut dependencies = Vec::new();
        for dep_line in dependencies_section.lines() {
            if dep_line.starts_with("- **D") {
                let parts: Vec<&str> = dep_line.split(':').collect();
                if parts.len() == 2 {
                    let id = parts[0]
                        .trim_start_matches("- **")
                        .trim_end_matches("**")
                        .to_string();
                    let dep_text = parts[1].trim();

                    // Parse "R3 depends on R2" format
                    if let Some((reqs, explanation)) = dep_text.split_once(" [") {
                        let reqs_parts: Vec<&str> = reqs.split(" depends on ").collect();
                        if reqs_parts.len() == 2 {
                            dependencies.push(Dependency {
                                id,
                                from_req: reqs_parts[0].trim().to_string(),
                                to_req: reqs_parts[1].trim().to_string(),
                                explanation: explanation.trim_end_matches(']').to_string(),
                            });
                        }
                    }
                }
            }
        }

        // Parse ambiguities
        let ambiguities_section = sections
            .iter()
            .find(|s| s.trim().starts_with("Notes on Ambiguities")).copied()
            .unwrap_or("");

        let ambiguities = ambiguities_section
            .lines()
            .filter(|l| l.starts_with('-'))
            .map(|l| l.trim_start_matches('-').trim().to_string())
            .collect();

        Ok(FunctionalRequirements { title, overview, requirements, dependencies, ambiguities })
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
    }
}
