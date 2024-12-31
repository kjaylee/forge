use std::sync::{Arc, RwLock};

use derive_more::derive::From;
use derive_setters::Setters;
use forge_prompt::Prompt;
use forge_provider::{
    CompletionMessage, ContentMessage, FinishReason, ModelId, Request, Response, ToolCall,
    ToolCallPart, ToolResult,
};
use serde::Serialize;

use crate::runtime::Application;
use crate::template::MessageTemplate;
use crate::Result;

#[derive(Clone, Debug, From)]
pub enum Action {
    UserMessage(ChatRequest),
    FileReadResponse(Vec<FileResponse>),
    AssistantResponse(Response),
    ToolResponse(ToolResult),
}

#[derive(Default, Debug, Clone, Setters)]
#[setters(into)]
pub struct FileResponse {
    pub path: String,
    pub content: String,
}

#[derive(Debug, serde::Deserialize, Clone, Setters)]
#[setters(into)]
#[serde(rename_all = "camelCase")]
pub struct ChatRequest {
    pub content: String,
    pub model: ModelId,
    pub conversation_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, derive_more::From)]
pub enum Command {
    #[from(ignore)]
    FileRead(Vec<String>),
    AssistantMessage(#[from] Request),
    UserMessage(#[from] ChatResponse),
    ToolUse(#[from] ToolCall),
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub enum ChatResponse {
    Text(String),
    ConversationId(String),
    ToolUseStart(ToolCallPart),
    ToolUseEnd(ToolResult),
    Complete,
    Fail(String),
}

#[derive(Default, Debug, Clone, Serialize, Setters)]
#[serde(rename_all = "camelCase")]
#[setters(strip_option)]
pub struct App {
    // The main objective that the user is trying to achieve
    pub user_objective: Option<MessageTemplate>,

    // A temp buffer used to store the assistant response (streaming mode only)
    pub assistant_buffer: String,

    // A temp buffer used to store the tool use parts (streaming mode only)
    pub tool_call_part: Vec<ToolCallPart>,
}

impl Application for App {
    type Action = Action;
    type Error = crate::Error;
    type Command = Command;
    type Context = Arc<RwLock<Request>>;

    fn run(
        mut self,
        context: Self::Context,
        action: impl Into<Action>,
    ) -> Result<(Self, Vec<Command>)> {
        let action = action.into();
        let mut commands = Vec::new();
        let mut context = context.write().unwrap();
        match action {
            Action::UserMessage(chat) => {
                let prompt = Prompt::parse(chat.content.clone())
                    .unwrap_or(Prompt::new(chat.content.clone()));

                *context = context.clone().model(chat.model.clone());

                if self.user_objective.is_none() {
                    self.user_objective = Some(MessageTemplate::task(prompt.clone()));
                }

                if prompt.files().is_empty() {
                    *context = context
                        .clone()
                        .add_message(CompletionMessage::user(chat.content));
                    commands.push(Command::AssistantMessage(context.clone()))
                } else {
                    commands.push(Command::FileRead(prompt.files()))
                }
            }
            Action::FileReadResponse(files) => {
                if let Some(message) = self.user_objective.clone() {
                    for fr in files.into_iter() {
                        *context = context.clone().add_message(
                            message
                                .clone()
                                .append(MessageTemplate::file(fr.path, fr.content)),
                        );
                    }

                    commands.push(Command::AssistantMessage(context.clone()))
                }
            }
            Action::AssistantResponse(response) => {
                let mut too_call_message: Option<ToolCall> = None;
                self.assistant_buffer.push_str(response.content.as_str());

                if !response.tool_call.is_empty() && self.tool_call_part.is_empty() {
                    if let Some(too_call_part) = response.tool_call.first() {
                        let too_call_start =
                            Command::UserMessage(ChatResponse::ToolUseStart(too_call_part.clone()));
                        commands.push(too_call_start)
                    }
                }

                self.tool_call_part.extend(response.tool_call);

                if let Some(FinishReason::ToolCall) = response.finish_reason {
                    let tool_call = ToolCall::try_from_parts(self.tool_call_part.clone())?;

                    // since tools is used, clear the tool_raw_arguments.
                    self.tool_call_part.clear();

                    too_call_message = Some(tool_call.clone());
                    commands.push(Command::ToolUse(tool_call));
                }

                if response.finish_reason.is_some() {
                    let mut message = ContentMessage::assistant(self.assistant_buffer.clone());
                    if let Some(tool_call) = too_call_message {
                        message = message.tool_call(tool_call);
                    }
                    *context = context.clone().add_message(message);
                    self.assistant_buffer.clear();
                }

                commands.push(Command::UserMessage(ChatResponse::Text(
                    response.content.to_string(),
                )));
            }
            Action::ToolResponse(tool_result) => {
                *context = context.clone().add_message(tool_result.clone());

                commands.push(Command::AssistantMessage(context.clone()));
                commands.push(Command::UserMessage(ChatResponse::ToolUseEnd(tool_result)));
            }
        };

        Ok((self, commands))
    }
}

#[cfg(test)]
mod tests {
    use forge_provider::{ContentMessage, ToolCallId};
    use forge_tool::ToolName;
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;
    use crate::template::Tag;

    impl ChatRequest {
        fn new(content: impl ToString) -> ChatRequest {
            ChatRequest { content: content.to_string(), model: ModelId::default(), conversation_id: None }
        }
    }

    trait Has: Sized {
        type Item;
        fn has(&self, other: impl Into<Self::Item>) -> bool;
    }

    impl Has for Vec<Command> {
        type Item = Command;
        fn has(&self, other: impl Into<Self::Item>) -> bool {
            let other: Self::Item = other.into();
            self.contains(&other)
        }
    }

    #[test]
    fn test_user_message_action() {
        let app = App::default();

        let chat_request = ChatRequest::new("Hello, world!");
        let chat_context = Arc::new(RwLock::new(Request::default()));
        let (_app, command) = app.run(chat_context.clone(), chat_request.clone()).unwrap();

        let ctx_reader = chat_context.read().unwrap();
        assert_eq!(ctx_reader.model, ModelId::default());
        assert!(command.has(Command::from(ctx_reader.clone())));
    }

    #[test]
    fn test_file_load_response_action() {
        let app = App::default().user_objective(MessageTemplate::new(
            Tag::default().name("test"),
            "Test message",
        ));

        let files = vec![FileResponse::default()
            .path("test_path.txt")
            .content("Test content")];

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_app, command) = app.run(chat_ctx.clone(), files.clone()).unwrap();

        let ctx_reader = chat_ctx.read().unwrap();
        assert!(ctx_reader.messages[0].content().contains(&files[0].path));
        assert!(ctx_reader.messages[0].content().contains(&files[0].content));
        assert!(command.has(Command::from(ctx_reader.clone())));
    }

    #[test]
    fn test_assistant_response_action_with_tool_call() {
        let app = App::default();

        let response = Response::new("Tool response")
            .tool_call(vec![ToolCallPart::default()
                .name(ToolName::new("test_tool"))
                .arguments_part(r#"{"key": "value"}"#)])
            .finish_reason(FinishReason::ToolCall);

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_, command) = app.run(chat_ctx, response).unwrap();

        assert!(command.has(ChatResponse::Text("Tool response".to_string())));
        assert!(command
            .has(ToolCall::new(ToolName::new("test_tool")).arguments(json!({"key": "value"}))));
    }

    #[test]
    fn test_use_tool_when_finish_reason_present() {
        let app = App::default();
        let response = Response::new("Tool response")
            .tool_call(vec![ToolCallPart::default()
                .call_id(ToolCallId::new("test_call_id"))
                .name(ToolName::new("fs_list"))
                .arguments_part(r#"{"path": "."}"#)])
            .finish_reason(FinishReason::ToolCall);

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, command) = app.run(chat_ctx, response).unwrap();

        assert!(app.tool_call_part.is_empty());

        assert!(command.has(
            ToolCall::new(ToolName::new("fs_list"))
                .call_id(ToolCallId::new("test_call_id"))
                .arguments(json!({"path": "."}))
        ));

        assert!(command.has(ChatResponse::Text("Tool response".to_string())));
    }

    #[test]
    fn test_should_not_use_tool_when_finish_reason_not_present() {
        let app = App::default();
        let resp = Response::new("Tool response").tool_call(vec![ToolCallPart::default()
            .name(ToolName::new("fs_list"))
            .arguments_part(r#"{"path": "."}"#)]);

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, command) = app.run(chat_ctx, resp).unwrap();

        assert!(!app.tool_call_part.is_empty());
        assert!(command.has(ChatResponse::Text("Tool response".to_string())));
    }

    #[test]
    fn test_should_set_user_objective_only_once() {
        let app = App::default();
        let request_0 = ChatRequest::new("Hello");
        let request_1 = ChatRequest::new("World");

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, _) = app.run(chat_ctx.clone(), request_0).unwrap();
        let (app, _) = app.run(chat_ctx.clone(), request_1).unwrap();

        assert_eq!(app.user_objective, Some(MessageTemplate::task("Hello")));
    }

    #[test]
    fn test_should_not_set_user_objective_if_already_set() {
        let app = App::default().user_objective(MessageTemplate::task("Initial Objective"));
        let request = ChatRequest::new("New Objective");

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, _) = app.run(chat_ctx, request).unwrap();

        assert_eq!(
            app.user_objective,
            Some(MessageTemplate::task("Initial Objective"))
        );
    }

    #[test]
    fn test_should_handle_file_read_response_with_multiple_files() {
        let app = App::default().user_objective(MessageTemplate::new(
            Tag::default().name("test"),
            "Test message",
        ));

        let files = vec![
            FileResponse::default()
                .path("file1.txt")
                .content("Content 1"),
            FileResponse::default()
                .path("file2.txt")
                .content("Content 2"),
        ];

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_app, command) = app.run(chat_ctx.clone(), files.clone()).unwrap();

        let ctx_reader = chat_ctx.read().unwrap();
        assert!(ctx_reader.messages[0].content().contains(&files[0].path));
        assert!(ctx_reader.messages[0].content().contains(&files[0].content));
        assert!(ctx_reader.messages[1].content().contains(&files[1].path));
        assert!(ctx_reader.messages[1].content().contains(&files[1].content));

        assert!(command.has(ctx_reader.clone()));
    }

    #[test]
    fn test_should_handle_assistant_response_with_no_tool_call() {
        let app = App::default();

        let response = Response::new("Assistant response")
            .tool_call(vec![])
            .finish_reason(FinishReason::EndTurn);

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, command) = app.run(chat_ctx, response).unwrap();

        assert!(app.tool_call_part.is_empty());
        assert!(command.has(ChatResponse::Text("Assistant response".to_string())));
    }

    #[test]

    fn test_too_call_seq() {
        let app = App::default();

        let message_1 = Action::AssistantResponse(
            Response::new("Let's use foo tool").add_tool_call(
                ToolCallPart::default()
                    .name(ToolName::new("foo"))
                    .arguments_part(r#"{"foo": 1,"#)
                    .call_id(ToolCallId::new("too_call_001")),
            ),
        );

        let message_2 = Action::AssistantResponse(
            Response::new("")
                .add_tool_call(ToolCallPart::default().arguments_part(r#""bar": 2}"#))
                .finish_reason(FinishReason::ToolCall),
        );

        let message_3 = Action::ToolResponse(
            ToolResult::new(ToolName::new("foo")).content(json!({"a": 100, "b": 200})),
        );

        // LLM made a tool_call request
        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_, _) = app
            .run_seq(chat_ctx.clone(), vec![message_1, message_2, message_3])
            .unwrap();

        let ctx_reader = chat_ctx.read().unwrap();
        assert_eq!(
            ctx_reader.messages[0],
            ContentMessage::assistant("Let's use foo tool")
                .tool_call(
                    ToolCall::new(ToolName::new("foo"))
                        .arguments(json!({"foo": 1, "bar": 2}))
                        .call_id(ToolCallId::new("too_call_001"))
                )
                .into()
        );
    }

    #[test]
    fn test_tool_result_seq() {
        let app = App::default();

        let message_1 = Action::AssistantResponse(
            Response::new("Let's use foo tool")
                .add_tool_call(
                    ToolCallPart::default()
                        .name(ToolName::new("foo"))
                        .arguments_part(r#"{"foo": 1, "bar": 2}"#)
                        .call_id(ToolCallId::new("too_call_001")),
                )
                .finish_reason(FinishReason::ToolCall),
        );

        let tool_result =
            ToolResult::new(ToolName::new("foo")).content(json!({"a": 100, "b": 200}));
        let message_2 = Action::ToolResponse(tool_result.clone());

        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_app, _) = app
            .run_seq(chat_ctx.clone(), vec![message_1, message_2])
            .unwrap();

        let ctx_reader = chat_ctx.read().unwrap();

        assert_eq!(
            ctx_reader.messages,
            vec![
                ContentMessage::assistant("Let's use foo tool")
                    .tool_call(
                        ToolCall::new(ToolName::new("foo"))
                            .arguments(json!({"foo": 1, "bar": 2}))
                            .call_id(ToolCallId::new("too_call_001"))
                    )
                    .into(),
                CompletionMessage::from(tool_result)
            ],
        );
    }

    #[test]
    fn test_think_tool_command() {
        let app = App::default();

        // Test when next thought is needed
        let think_result_continue = ToolResult::new(ToolName::new("think")).content(json!({
            "thoughtNumber": 1,
            "totalThoughts": 3,
            "nextThoughtNeeded": true,
            "branches": [],
            "thoughtHistoryLength": 1
        }));

        let action = Action::ToolResponse(think_result_continue);
        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, commands) = app.run(chat_ctx.clone(), action).unwrap();

        assert!(commands.has(Command::AssistantMessage(chat_ctx.read().unwrap().clone())));

        // Test when thinking is complete
        let think_result_end = ToolResult::new(ToolName::new("think")).content(json!({
            "thoughtNumber": 3,
            "totalThoughts": 3,
            "nextThoughtNeeded": false,
            "branches": [],
            "thoughtHistoryLength": 3
        }));

        let action = Action::ToolResponse(think_result_end.clone());
        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (_, commands) = app.run(chat_ctx.clone(), action).unwrap();

        assert!(commands.has(Command::AssistantMessage(chat_ctx.read().unwrap().clone())));
        assert!(commands.has(Command::UserMessage(ChatResponse::ToolUseEnd(
            think_result_end
        ))));
    }

    #[test]
    fn test_think_tool_state() {
        let app = App::default();

        // Test when next thought is needed
        let think_result_continue = ToolResult::new(ToolName::new("think")).content(json!({
            "thoughtNumber": 1,
            "totalThoughts": 3,
            "nextThoughtNeeded": true,
            "branches": [],
            "thoughtHistoryLength": 1
        }));

        let action = Action::ToolResponse(think_result_continue.clone());
        let chat_ctx = Arc::new(RwLock::new(Request::default()));
        let (app, _) = app.run(chat_ctx.clone(), action).unwrap();

        // Should only push AssistantMessage to continue conversation

        // Test when thinking is complete
        let think_result_end = ToolResult::new(ToolName::new("think")).content(json!({
            "thoughtNumber": 3,
            "totalThoughts": 3,
            "nextThoughtNeeded": false,
            "branches": [],
            "thoughtHistoryLength": 3
        }));

        let action = Action::ToolResponse(think_result_end.clone());
        let (_, _) = app.run(chat_ctx.clone(), action).unwrap();

        assert_eq!(
            chat_ctx.read().unwrap().messages,
            vec![think_result_continue.clone(), think_result_end]
                .into_iter()
                .map(CompletionMessage::from)
                .collect::<Vec<_>>()
        );
    }

    // #[test]
    // fn test_context_initial_message() {
    //     let app = App::default();

    //     assert_eq!(app.request.messages.len(), 0);
    // }
}
