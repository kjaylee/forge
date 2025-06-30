use serde::{Deserialize, Serialize};

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ForgeConfig {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub choices: Option<ChoicesConfig>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ChoiceType {
    Allow,
    Reject,
    #[default]
    AskEveryTime,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChoicesConfig {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execute_shell_commands: Option<ChoiceType>,
}
