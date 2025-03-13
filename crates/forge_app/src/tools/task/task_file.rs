use std::path::PathBuf;

use anyhow::Result;
use chrono::Utc;
use forge_domain::TaskStatus;

/// Manages the task file (.task.md)
pub struct TaskFile;

impl TaskFile {
    /// Creates a new task file for an issue or updates an existing one
    pub async fn create_for_issue(
        issue_number: u32,
        issue_title: &str,
        issue_url: &str,
        issue_description: &str,
        min_proposals: u32,
        custom_title: Option<&str>,
    ) -> Result<PathBuf> {
        let path = PathBuf::from(".task.md");
        let now = Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string();

        // Check if the file already exists
        if path.exists() {
            println!(
                "Task file already exists at {}, updating it",
                path.display()
            );

            // Read the existing file content
            let existing_content = tokio::fs::read_to_string(&path).await?;

            // Extract existing sections
            let mut sections = Self::extract_sections(&existing_content);

            // Only update the timestamp in the current status section
            if let Some(status_section) = sections.get_mut("Current Status") {
                // Replace the last updated line
                let updated_status = status_section
                    .lines()
                    .map(|line| {
                        if line.starts_with("**Last Updated**:") {
                            format!("**Last Updated**: {}", now)
                        } else {
                            line.to_string()
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                sections.insert("Current Status", updated_status);
            }

            // Rebuild the content and write it back
            let updated_content = Self::rebuild_content(sections);
            tokio::fs::write(&path, updated_content).await?;

            return Ok(path);
        }

        // Use custom title or generate one from issue title
        let title = custom_title.unwrap_or(issue_title);

        // Create the task file content
        #[allow(clippy::format_in_format_args)]
        let content = format!(
            "# Task: Fix Issue #{} - {}\n\n\
            ## Issue Details\n\
            **URL**: {}\n\
            **Created At**: {}\n\
            **Status**: {}\n\n\
            {}\n\n\
            ## Plan\n\
            1. [ ] Analyze the issue and root cause\n\
            2. [ ] Implement fix\n\
            3. [ ] Add tests to prevent regression\n\
            4. [ ] Update documentation\n\n\
            ## Proposals\n\
            *At least {} proposals should be generated*\n\n\
            ### Proposal 1: [Title]\n\
            Description of approach 1...\n\n\
            ## Current Status\n\
            **Status**: {}\n\
            **Last Updated**: {}\n",
            issue_number,
            title,
            issue_url,
            now,
            "OPEN",
            issue_description,
            min_proposals,
            format!("{:?}", TaskStatus::Planned),
            now
        );

        // Write the content to the task file
        tokio::fs::write(&path, content).await?;

        Ok(path)
    }

    /// Updates a task file with updated information
    pub async fn update(
        pr_number: u32,
        path: &PathBuf,
        comments: Vec<(String, String, String)>, // (username, timestamp, comment)
        status: TaskStatus,
    ) -> Result<()> {
        // Read the existing task file
        let content = tokio::fs::read_to_string(path).await?;

        // Extract sections we want to preserve
        let mut sections = Self::extract_sections(&content);

        // Update the status
        sections.insert(
            "Current Status",
            Self::create_status_section(pr_number, &status),
        );

        // Add the comments section
        sections.insert("Recent Comments", Self::create_comments_section(comments));

        // Rebuild the file content
        let updated_content = Self::rebuild_content(sections);

        // Write the updated content back to the file
        tokio::fs::write(path, updated_content).await?;

        Ok(())
    }

    // Helper function to extract sections from the task file
    fn extract_sections(content: &str) -> std::collections::HashMap<&str, String> {
        let mut sections = std::collections::HashMap::new();
        let mut current_section = "";
        let mut section_content = String::new();

        for line in content.lines() {
            if line.starts_with("## ") {
                // Save the previous section if there was one
                if !current_section.is_empty() && !section_content.is_empty() {
                    sections.insert(current_section, section_content.trim().to_string());
                    section_content = String::new();
                }

                // Start a new section
                current_section = line.trim_start_matches("## ");
            } else if !current_section.is_empty() {
                section_content.push_str(line);
                section_content.push('\n');
            }
        }

        // Save the last section
        if !current_section.is_empty() && !section_content.is_empty() {
            sections.insert(current_section, section_content.trim().to_string());
        }

        sections
    }

    // Helper function to create the status section
    fn create_status_section(pr_number: u32, status: &TaskStatus) -> String {
        let now = Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string();

        format!(
            "**Status**: {:?}\n\
            **PR**: #{}\n\
            **Last Updated**: {}\n",
            status, pr_number, now
        )
    }

    // Helper function to create the comments section
    fn create_comments_section(comments: Vec<(String, String, String)>) -> String {
        let mut section = String::new();

        for (username, timestamp, comment) in comments {
            section.push_str(&format!(
                "> **{}** ({}):\n\
                > {}\n\n",
                username, timestamp, comment
            ));
        }

        if section.is_empty() {
            section = "No recent comments.".to_string();
        }

        section
    }

    // Helper function to rebuild the content
    fn rebuild_content(sections: std::collections::HashMap<&str, String>) -> String {
        let mut content = String::new();

        // Add the title section
        if let Some(title) = sections.get("Task") {
            content.push_str(&format!("# {}\n\n", title));
        }

        // Define the order of sections
        let section_order = [
            "Issue Details",
            "Plan",
            "Proposals",
            "Current Status",
            "Recent Comments",
        ];

        // Add each section in the defined order
        for section in section_order.iter() {
            if let Some(section_content) = sections.get(section) {
                content.push_str(&format!("## {}\n{}\n\n", section, section_content));
            }
        }

        // Add any remaining sections not in the predefined order
        for (section, section_content) in sections.iter() {
            if !section_order.contains(section) && *section != "Task" {
                content.push_str(&format!("## {}\n{}\n\n", section, section_content));
            }
        }

        content
    }
}
