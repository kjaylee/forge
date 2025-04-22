use std::fmt::{self, Display, Formatter};

use chrono::{DateTime, Local};
use colored::Colorize;
use derive_setters::Setters;

#[derive(Clone, Setters)]
#[setters(into, strip_option)]
pub struct TitleFormat {
    pub title: String,
    pub sub_title: Option<String>,
    pub error: Option<String>,
    pub is_user_action: bool,
    pub timestamp: DateTime<Local>,
}

pub trait TitleExt {
    fn title_fmt(&self) -> TitleFormat;
}

impl<T> TitleExt for T
where
    T: Into<TitleFormat> + Clone,
{
    fn title_fmt(&self) -> TitleFormat {
        self.clone().into()
    }
}

impl TitleFormat {
    /// Create a status for executing a tool
    pub fn new(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            error: None,
            sub_title: Default::default(),
            is_user_action: false,
            timestamp: Local::now(),
        }
    }

    /// Create a status for executing a tool
    pub fn action(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            error: None,
            sub_title: Default::default(),
            is_user_action: true,
            timestamp: Local::now(), // Still set timestamp even for user actions
        }
    }

    pub fn format(&self) -> String {
        let mut buf = String::new();

        // Add timestamp at the beginning if this is not a user action
        if !self.is_user_action {
            buf.push_str(&format!(
                "{} ",
                self.timestamp.format("%H:%M:%S.%3f").to_string().dimmed()
            ));
        }

        if self.is_user_action {
            buf.push_str(format!("{} ", "⏺".yellow()).as_str());
        } else {
            buf.push_str(format!("{} ", "⏺".dimmed()).as_str());
        }
        let mut title = self.title.dimmed();

        if self.error.is_some() {
            title = title.red().bold();
        }

        buf.push_str(&format!("{title}"));

        if let Some(ref sub_title) = self.sub_title {
            buf.push_str(&format!(" {}", sub_title.dimmed()).to_string());
        }

        if let Some(ref error) = self.error {
            buf.push_str(&format!(" {error}").to_string());
        }

        buf
    }
}

impl Display for TitleFormat {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format())
    }
}
