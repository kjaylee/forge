use std::fmt::{self, Display, Formatter};

use colored::Colorize;
use derive_setters::Setters;
use forge_domain::Usage;

#[derive(Clone)]
pub enum Kind {
    Execute,
    Success,
    Failed,
}

impl Kind {
    fn icon(&self) -> &'static str {
        match self {
            Kind::Execute => "⚙",
            Kind::Success => "✓",
            Kind::Failed => "✗",
        }
    }

    fn label(&self) -> &'static str {
        match self {
            Kind::Execute => "execute",
            Kind::Success => "success",
            Kind::Failed => "error",
        }
    }
}

#[derive(Clone, Setters)]
pub struct TitleFormat {
    pub kind: Kind,
    pub message: String,
    pub error_details: Option<String>,
    #[setters(into)]
    pub usage: Usage,
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
    pub fn execute(message: impl Into<String>) -> Self {
        Self {
            kind: Kind::Execute,
            message: message.into(),
            error_details: None,
            usage: Usage::default(),
        }
    }

    /// Create a success status
    pub fn success(message: impl Into<String>) -> Self {
        Self {
            kind: Kind::Success,
            message: message.into(),
            error_details: None,
            usage: Usage::default(),
        }
    }

    /// Create a failure status
    pub fn failed(message: impl Into<String>) -> Self {
        Self {
            kind: Kind::Failed,
            message: message.into(),
            error_details: None,
            usage: Usage::default(),
        }
    }

    pub fn format(&self) -> String {
        let (icon, label, message) = match self.kind {
            Kind::Execute => (
                self.icon().cyan(),
                self.label().bold().cyan(),
                format!("{} ", self.message),
            ),
            Kind::Success => (
                self.icon().green(),
                self.label().bold().green(),
                self.message.to_string(),
            ),
            Kind::Failed => {
                let error_suffix = self
                    .error_details
                    .as_ref()
                    .map(|e| format!(" ({})", e))
                    .unwrap_or_default();
                (
                    self.icon().red(),
                    self.label().bold().red(),
                    format!("{}{}", self.message, error_suffix.red()),
                )
            }
        };

        let timestamp = chrono::Local::now().format("%H:%M:%S%.3f").to_string();
        let mut result = format!("{} {} {} {}", timestamp.dimmed(), icon, label, message);

        if self.usage.total_tokens > 0 {
            result.push_str(
                &format!(
                    " [tokens {}/{}/{}]",
                    self.usage.prompt_tokens, self.usage.completion_tokens, self.usage.total_tokens
                )
                .dimmed()
                .to_string(),
            );
        }

        result
    }

    fn icon(&self) -> &'static str {
        self.kind.icon()
    }

    fn label(&self) -> &'static str {
        self.kind.label()
    }
}

impl Display for TitleFormat {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format())
    }
}
