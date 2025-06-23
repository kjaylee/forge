use ratatui::layout::Alignment;
use ratatui::style::{Color, Stylize};
use ratatui::text::{Line, Span};

pub struct StatusBar {
    editor_status: Option<String>,
    agent: Option<String>,
    current_branch: Option<String>,
    current_dir: Option<String>,
}

impl StatusBar {
    /// Create a new StatusBar with all fields
    pub fn new(
        agent: impl ToString,
        editor_status: impl ToString,
        current_branch: Option<String>,
        current_dir: Option<String>,
    ) -> Self {
        Self {
            editor_status: Some(editor_status.to_string()),
            agent: Some(agent.to_string()),
            current_branch,
            current_dir,
        }
    }

    /// Create a minimal StatusBar with only branch and directory information
    /// This is useful for Settings and Help views where editor status is not
    /// relevant
    pub fn minimal(current_branch: Option<String>, current_dir: Option<String>) -> Self {
        Self {
            editor_status: None,
            agent: None,
            current_branch,
            current_dir,
        }
    }

    /// Create an empty StatusBar
    pub fn empty() -> Self {
        Self {
            editor_status: None,
            agent: None,
            current_branch: None,
            current_dir: None,
        }
    }
}

impl<'a> From<StatusBar> for Line<'a> {
    fn from(value: StatusBar) -> Self {
        let space = Span::from(" ");
        let mut spans = vec![space.clone()];

        // Add editor status if available
        if let Some(editor_status) = value.editor_status {
            let bg_color = if editor_status.to_lowercase() == "insert" {
                Color::Green
            } else {
                Color::White
            };
            spans.push(Span::from(format!(" {} ", editor_status.to_uppercase())).bg(bg_color));
            spans.push(space.clone());
        }

        // Add agent if available
        if let Some(agent) = value.agent {
            spans.push(Span::from(format!(" {} ", agent.to_uppercase())).bg(Color::White));
            spans.push(space.clone());
        }

        // Check if we have both branch and directory for spacing logic
        let has_branch = value.current_branch.is_some();

        // Add branch information if available
        if let Some(branch) = value.current_branch {
            spans.push(Span::from(branch.to_string()).fg(Color::LightGreen));
        }

        // Add directory information if available (show only the directory name, not
        // full path)
        if let Some(dir) = value.current_dir {
            // Add space before directory if branch was added
            if has_branch {
                spans.push(space.clone());
            }
            let dir_name = std::path::Path::new(&dir)
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or(&dir);
            spans.push(Span::from(format!("{dir_name} ")).fg(Color::LightCyan));
        }

        Line::from(spans).alignment(Alignment::Left).bold()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::text::Span;

    use super::*;

    #[test]
    fn test_status_bar_full() {
        let fixture = StatusBar::new(
            "FORGE",
            "INSERT",
            Some("main".to_string()),
            Some("/home/user".to_string()),
        );
        let actual: Line = fixture.into();
        let expected = Line::from(vec![
            Span::from(" "),
            Span::from(" INSERT ").bg(Color::Green),
            Span::from(" "),
            Span::from(" FORGE ").bg(Color::White),
            Span::from(" "),
            Span::from("main").fg(Color::LightGreen),
            Span::from(" "),
            Span::from("user ").fg(Color::LightCyan),
        ])
        .alignment(Alignment::Left)
        .bold();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_status_bar_minimal() {
        let fixture = StatusBar::minimal(Some("main".to_string()), Some("/home/user".to_string()));
        let actual: Line = fixture.into();
        let expected = Line::from(vec![
            Span::from(" "),
            Span::from("main").fg(Color::LightGreen),
            Span::from(" "),
            Span::from("user ").fg(Color::LightCyan),
        ])
        .alignment(Alignment::Left)
        .bold();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_status_bar_empty() {
        let fixture = StatusBar::empty();
        let actual: Line = fixture.into();
        let expected = Line::from(vec![Span::from(" ")])
            .alignment(Alignment::Left)
            .bold();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_status_bar_branch_only() {
        let fixture = StatusBar::minimal(Some("develop".to_string()), None);
        let actual: Line = fixture.into();
        let expected = Line::from(vec![
            Span::from(" "),
            Span::from("develop").fg(Color::LightGreen),
        ])
        .alignment(Alignment::Left)
        .bold();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_status_bar_dir_only() {
        let fixture = StatusBar::minimal(None, Some("/home/user/project".to_string()));
        let actual: Line = fixture.into();
        let expected = Line::from(vec![
            Span::from(" "),
            Span::from("project ").fg(Color::LightCyan),
        ])
        .alignment(Alignment::Left)
        .bold();
        assert_eq!(actual, expected);
    }
}
