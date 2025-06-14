use crate::execution_result::ExecutionResult;
use crate::input_title::Content;
use crate::utils::format_match;
use forge_display::{DiffFormat, GrepFormat};
use forge_domain::{Environment, Tools};
use regex::Regex;

pub trait OutputTitle {
    fn to_content(&self, input: Tools, env: &Environment) -> Content;
}

impl OutputTitle for ExecutionResult {
    fn to_content(&self, input: Tools, env: &Environment) -> Content {
        match (self, input) {
            (ExecutionResult::FsCreate(out), Tools::ForgeToolFsCreate(input)) => {
                let new_content = input.content;
                if let Some(old_content) = out.previous.as_ref() {
                    let diff = DiffFormat::format(old_content, &new_content);
                    return Content::Summary(diff);
                }

                Content::None
            }
            (ExecutionResult::FsSearch(output), Tools::ForgeToolFsSearch(input)) => {
                if let Some(output) = output.as_ref() {
                    let mut formatted_ = GrepFormat::new(
                        output
                            .matches
                            .iter()
                            .map(|v| format_match(v, &env))
                            .collect::<Vec<_>>(),
                    );
                    if let Some(regex) = input.regex.as_ref().and_then(|v| Regex::new(v).ok()) {
                        formatted_ = formatted_.regex(regex);
                    }

                    return Content::Summary(formatted_.format());
                }

                Content::None
            }
            (ExecutionResult::FsPatch(output), Tools::ForgeToolFsPatch(_)) => {
                let diff = DiffFormat::format(&output.before, &output.after);
                Content::Summary(diff)
            }
            (ExecutionResult::FsRead(_), Tools::ForgeToolFsRead(_)) => Content::None,
            (ExecutionResult::FsRemove(_), Tools::ForgeToolFsRemove(_)) => Content::None,
            (ExecutionResult::FsUndo(_), Tools::ForgeToolFsUndo(_)) => Content::None,
            (ExecutionResult::NetFetch(_), Tools::ForgeToolNetFetch(_)) => Content::None,
            (ExecutionResult::Shell(_), Tools::ForgeToolProcessShell(_)) => Content::None,
            (ExecutionResult::FollowUp(_), Tools::ForgeToolFollowup(_)) => Content::None,
            (ExecutionResult::AttemptCompletion, _) => Content::None,
            _ => Content::None,
        }
    }
}
