use derive_more::Display;
use serde::{Deserialize, Serialize};
use strum_macros::EnumIter;

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ForgeConfig {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub choices: Option<ChoicesConfig>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize, Display, PartialEq, EnumIter)]
#[serde(rename_all = "camelCase")]
pub enum ChoiceType {
    Allow,
    Reject,
    #[default]
    #[display("Ask every time")]
    AskEveryTime,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChoicesConfig {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execute_shell_commands: Option<ChoiceType>,
}
#[derive(Clone, Debug, Display, EnumIter)]
pub enum ConfigOption {
    #[display("Shell Command Execution")]
    ShellCommandExecution,
}
