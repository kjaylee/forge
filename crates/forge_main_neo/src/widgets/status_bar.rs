use ratatui::layout::Alignment;
use ratatui::style::{Color, Stylize};
use ratatui::text::{Line, Span};

pub struct StatusBar {
    editor_status: String,
    agent: String,
    current_branch: Option<String>,
    current_dir: Option<String>,
}

impl StatusBar {
    pub fn new(
        agent: impl ToString,
        editor_status: impl ToString,
        current_branch: Option<String>,
        current_dir: Option<String>,
    ) -> Self {
        Self {
            editor_status: editor_status.to_string(),
            agent: agent.to_string(),
            current_branch,
            current_dir,
        }
    }
}

impl<'a> From<StatusBar> for Line<'a> {
    fn from(value: StatusBar) -> Self {
        let space = Span::from(" ");
        let bg_color = if value.editor_status.to_lowercase() == "insert" {
            Color::Green
        } else {
            Color::White
        };

        let mut spans = vec![
            space.clone(),
            Span::from(format!(" {} ", value.editor_status.to_uppercase())).bg(bg_color),
            space.clone(),
            Span::from(format!(" {} ", value.agent.to_uppercase())).bg(Color::White),
            space.clone(),
        ];

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
