use std::sync::Arc;

use anyhow::Context;
use forge_domain::{TaskList, ToolCallContext, ToolCallFull, ToolOutput, Tools};

use crate::error::Error;
use crate::fmt_input::{FormatInput, InputFormat};
use crate::fmt_output::FormatOutput;
use crate::operation::Operation;
use crate::services::ShellService;
use crate::{
    ConversationService, EnvironmentService, FollowUpService, FsCreateService, FsPatchService,
    FsReadService, FsRemoveService, FsSearchService, FsUndoService, NetFetchService,
    TaskListOutput,
};

pub struct ToolExecutor<S> {
    services: Arc<S>,
}

impl<
    S: FsReadService
        + FsCreateService
        + FsSearchService
        + NetFetchService
        + FsRemoveService
        + FsPatchService
        + FsUndoService
        + ShellService
        + FollowUpService
        + ConversationService
        + EnvironmentService,
> ToolExecutor<S>
{
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }

    async fn call_internal(
        &self,
        input: Tools,
        task_list: &mut TaskList,
    ) -> anyhow::Result<Operation> {
        Ok(match input {
            Tools::ForgeToolFsRead(input) => {
                let output = self
                    .services
                    .read(
                        input.path.clone(),
                        input.start_line.map(|i| i as u64),
                        input.end_line.map(|i| i as u64),
                    )
                    .await?;
                (input, output).into()
            }
            Tools::ForgeToolFsCreate(input) => {
                let output = self
                    .services
                    .create(
                        input.path.clone(),
                        input.content.clone(),
                        input.overwrite,
                        true,
                    )
                    .await?;
                (input, output).into()
            }
            Tools::ForgeToolFsSearch(input) => {
                let output = self
                    .services
                    .search(
                        input.path.clone(),
                        input.regex.clone(),
                        input.file_pattern.clone(),
                    )
                    .await?;
                (input, output).into()
            }
            Tools::ForgeToolFsRemove(input) => {
                let _output = self.services.remove(input.path.clone()).await?;
                input.into()
            }
            Tools::ForgeToolFsPatch(input) => {
                let output = self
                    .services
                    .patch(
                        input.path.clone(),
                        input.search.clone(),
                        input.operation.clone(),
                        input.content.clone(),
                    )
                    .await?;
                (input, output).into()
            }
            Tools::ForgeToolFsUndo(input) => {
                let output = self.services.undo(input.path.clone()).await?;
                (input, output).into()
            }
            Tools::ForgeToolProcessShell(input) => {
                let output = self
                    .services
                    .execute(input.command.clone(), input.cwd.clone(), input.keep_ansi)
                    .await?;
                output.into()
            }
            Tools::ForgeToolNetFetch(input) => {
                let output = self.services.fetch(input.url.clone(), input.raw).await?;
                (input, output).into()
            }
            Tools::ForgeToolFollowup(input) => {
                let output = self
                    .services
                    .follow_up(
                        input.question.clone(),
                        input
                            .option1
                            .clone()
                            .into_iter()
                            .chain(input.option2.clone().into_iter())
                            .chain(input.option3.clone().into_iter())
                            .chain(input.option4.clone().into_iter())
                            .chain(input.option5.clone().into_iter())
                            .collect(),
                        input.multiple,
                    )
                    .await?;
                output.into()
            }
            Tools::ForgeToolAttemptCompletion(_input) => {
                crate::operation::Operation::AttemptCompletion
            }
            Tools::ForgeToolTaskList(input) => {
                let output = match &input.operation {
                    forge_domain::TaskListOperation::Append { task } => {
                        let (task, stats) = task_list.append(task);
                        TaskListOutput::TaskAdded {
                            task,
                            stats,
                            message: "Task appended to the list.".to_string(),
                        }
                    }
                    forge_domain::TaskListOperation::Prepend { task } => {
                        let (task, stats) = task_list.prepend(task);
                        TaskListOutput::TaskAdded {
                            task,
                            stats,
                            message: "Task prepended to the list.".to_string(),
                        }
                    }
                    forge_domain::TaskListOperation::PopFront => {
                        let (task, stats) = task_list.pop_front().context("Task list is empty")?;
                        TaskListOutput::TaskPopped {
                            task,
                            stats,
                            message: "Task popped from the front of the list.".to_string(),
                        }
                    }
                    forge_domain::TaskListOperation::PopBack => match task_list.pop_back() {
                        Some((task, stats)) => TaskListOutput::TaskPopped {
                            task,
                            stats,
                            message: "Task popped from the back of the list.".to_string(),
                        },
                        None => {
                            TaskListOutput::Error { message: "Task list is empty.".to_string() }
                        }
                    },
                    forge_domain::TaskListOperation::MarkDone { task_id } => {
                        let result = task_list.mark_done(*task_id);
                        if let Some((completed_task, next_task, stats)) = result {
                            TaskListOutput::TaskCompleted {
                                completed_task,
                                next_task,
                                stats,
                                message: "Task marked as done.".to_string(),
                            }
                        } else {
                            TaskListOutput::Error { message: "Task not found.".to_string() }
                        }
                    }
                    forge_domain::TaskListOperation::List => {
                        let markdown = task_list.to_markdown();
                        let stats = task_list.stats();
                        TaskListOutput::TaskList { markdown, stats }
                    }
                    forge_domain::TaskListOperation::Clear => {
                        task_list.clear();
                        TaskListOutput::Cleared { message: "Task list cleared.".to_string() }
                    }
                    forge_domain::TaskListOperation::Stats => {
                        let stats = task_list.stats();
                        TaskListOutput::StatsOnly { stats }
                    }
                };

                Operation::TaskList { _input: input, output }
            }
        })
    }

    pub async fn execute(
        &self,
        input: ToolCallFull,
        context: &mut ToolCallContext,
    ) -> anyhow::Result<ToolOutput> {
        let tool_input = Tools::try_from(input).map_err(Error::CallArgument)?;
        let env = self.services.get_environment();
        match tool_input.to_content(&env) {
            InputFormat::Title(title) => context.send_text(title).await?,
            InputFormat::Summary(summary) => context.send_summary(summary).await?,
        };

        // Send tool call information

        let execution_result = self
            .call_internal(tool_input.clone(), &mut context.task_list)
            .await;
        if let Err(ref error) = execution_result {
            tracing::error!(error = ?error, "Tool execution failed");
        }

        let execution_result = execution_result?;

        // Send formatted output message
        if let Some(output) = execution_result.to_content(&env) {
            context.send_text(output).await?;
        }

        let truncation_path = execution_result
            .to_create_temp(self.services.as_ref())
            .await?;

        Ok(execution_result.into_tool_output(truncation_path, &env))
    }
}
