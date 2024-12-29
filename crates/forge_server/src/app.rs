use derive_more::derive::From;
use derive_setters::Setters;
use forge_prompt::Prompt;
use forge_provider::{
    ChatMessage, FinishReason, ModelId, Request, RequestMessage, Response, ToolResult, ToolUse,
    ToolUsePart,
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

#[derive(Default, Debug, serde::Deserialize, Clone, Setters)]
#[setters(into)]
pub struct ChatRequest {
    pub message: String,
    pub model: ModelId,
}

#[derive(Debug, Clone, PartialEq, derive_more::From)]
pub enum Command {
    #[from(ignore)]
    FileRead(Vec<String>),
    AssistantMessage(#[from] Request),
    UserMessage(#[from] ChatResponse),
    ToolUse(#[from] ToolUse),
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub enum ChatResponse {
    Text(String),
    ToolUseStart(ToolUsePart),
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
    pub tool_use_part: Vec<ToolUsePart>,

    // Keep context at the end so that debugging the Serialized format is easier
    pub request: Request,
}

impl App {
    pub fn new(context: Request) -> Self {
        Self {
            request: context,
            user_objective: None,
            tool_use_part: Vec::new(),
            assistant_buffer: "".to_string(),
        }
    }
}

impl Application for App {
    type Action = Action;
    type Error = crate::Error;
    type Command = Command;

    fn run(mut self, action: impl Into<Action>) -> Result<(Self, Vec<Command>)> {
        let action = action.into();
        let mut commands = Vec::new();
        match action {
            Action::UserMessage(chat) => {
                let prompt = Prompt::parse(chat.message.clone())
                    .unwrap_or(Prompt::new(chat.message.clone()));

                self.request = self.request.model(chat.model.clone());

                if self.user_objective.is_none() {
                    self.user_objective = Some(MessageTemplate::task(prompt.clone()));
                }

                if prompt.files().is_empty() {
                    self.request = self.request.add_message(RequestMessage::user(chat.message));
                    commands.push(Command::AssistantMessage(self.request.clone()))
                } else {
                    commands.push(Command::FileRead(prompt.files()))
                }
            }
            Action::FileReadResponse(files) => {
                if let Some(message) = self.user_objective.clone() {
                    for fr in files.into_iter() {
                        self.request = self.request.add_message(
                            message
                                .clone()
                                .append(MessageTemplate::file(fr.path, fr.content)),
                        );
                    }

                    commands.push(Command::AssistantMessage(self.request.clone()))
                }
            }
            Action::AssistantResponse(response) => {
                let mut tool_use_message: Option<ToolUse> = None;
                self.assistant_buffer
                    .push_str(response.message.as_str());

                if !response.tool_use.is_empty() && self.tool_use_part.is_empty() {
                    if let Some(tool_use_part) = response.tool_use.first() {
                        let tool_use_start =
                            Command::UserMessage(ChatResponse::ToolUseStart(tool_use_part.clone()));
                        commands.push(tool_use_start)
                    }
                }

                self.tool_use_part.extend(response.tool_use);

                if let Some(FinishReason::ToolUse) = response.finish_reason {
                    let tool_use = ToolUse::try_from_parts(self.tool_use_part.clone())?;

                    // since tools is used, clear the tool_raw_arguments.
                    self.tool_use_part.clear();

                    tool_use_message = Some(tool_use.clone());
                    commands.push(Command::ToolUse(tool_use));
                }

                if response.finish_reason.is_some() {
                    let mut message = ChatMessage::assistant(self.assistant_buffer.clone());
                    if let Some(tool_use) = tool_use_message {
                        message = message.tool_use(tool_use);
                    }
                    self.request = self.request.add_message(message);
                    self.assistant_buffer.clear();
                }

                commands.push(Command::UserMessage(ChatResponse::Text(
                    response.message.to_string(),
                )));
            }
            Action::ToolResponse(tool_result) => {
                self.request = self.request.add_message(tool_result.clone());

                commands.push(Command::AssistantMessage(self.request.clone()));
                commands.push(Command::UserMessage(ChatResponse::ToolUseEnd(tool_result)));
            }
        };
        Ok((self, commands))
    }
}

#[cfg(test)]
mod tests {
    use forge_provider::{ChatMessage, ToolUseId};
    use forge_tool::ToolName;
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;
    use crate::template::Tag;

    #[test]
    fn test_user_message_action() {
        let app = App::default();

        let chat_request = ChatRequest::default().message("Hello, world!");

        let (app, command) = app.run(chat_request.clone()).unwrap();

        assert_eq!(&app.request.model, &ModelId::default());
        assert!(command.has(app.request.clone()));
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

        let (app, command) = app.run(files.clone()).unwrap();

        assert!(app.request.messages[0].content().contains(&files[0].path));
        assert!(app.request.messages[0]
            .content()
            .contains(&files[0].content));

        assert!(command.has(app.request.clone()));
    }

    #[test]
    fn test_assistant_response_action_with_tool_use() {
        let app = App::default();

        let response = Response::new("Tool response")
            .tool_use(vec![ToolUsePart::default()
                .name(ToolName::new("test_tool"))
                .arguments_part(r#"{"key": "value"}"#)])
            .finish_reason(FinishReason::ToolUse);

        let (_, command) = app.run(response).unwrap();

        assert!(command.has(ChatResponse::Text("Tool response".to_string())));

        assert!(command
            .has(ToolUse::new(ToolName::new("test_tool")).arguments(json!({"key": "value"}))));
    }

    #[test]
    fn test_use_tool_when_finish_reason_present() {
        let app = App::default();
        let response = Response::new("Tool response")
            .tool_use(vec![ToolUsePart::default()
                .use_id(ToolUseId::new("test_use_id"))
                .name(ToolName::new("fs_list"))
                .arguments_part(r#"{"path": "."}"#)])
            .finish_reason(FinishReason::ToolUse);

        let (app, command) = app.run(response).unwrap();

        assert!(app.tool_use_part.is_empty());

        assert!(command.has(
            ToolUse::new(ToolName::new("fs_list"))
                .use_id(ToolUseId::new("test_use_id"))
                .arguments(json!({"path": "."}))
        ));

        assert!(command.has(ChatResponse::Text("Tool response".to_string())));
    }

    #[test]
    fn test_should_not_use_tool_when_finish_reason_not_present() {
        let app = App::default();
        let resp = Response::new("Tool response").tool_use(vec![ToolUsePart::default()
            .name(ToolName::new("fs_list"))
            .arguments_part(r#"{"path": "."}"#)]);

        let (app, command) = app.run(resp).unwrap();

        assert!(!app.tool_use_part.is_empty());
        assert!(command.has(ChatResponse::Text("Tool response".to_string())));
    }

    #[test]
    fn test_should_set_user_objective_only_once() {
        let app = App::default();
        let request_0 = ChatRequest::default().message("Hello");
        let request_1 = ChatRequest::default().message("World");

        let (app, _) = app.run(request_0).unwrap();
        let (app, _) = app.run(request_1).unwrap();

        assert_eq!(app.user_objective, Some(MessageTemplate::task("Hello")));
    }

    #[test]
    fn test_should_not_set_user_objective_if_already_set() {
        let app = App::default().user_objective(MessageTemplate::task("Initial Objective"));
        let request = ChatRequest::default().message("New Objective");

        let (app, _) = app.run(request).unwrap();

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

        let (app, command) = app.run(files.clone()).unwrap();

        assert!(app.request.messages[0].content().contains(&files[0].path));
        assert!(app.request.messages[0]
            .content()
            .contains(&files[0].content));
        assert!(app.request.messages[1].content().contains(&files[1].path));
        assert!(app.request.messages[1]
            .content()
            .contains(&files[1].content));

        assert!(command.has(app.request.clone()));
    }

    #[test]
    fn test_should_handle_assistant_response_with_no_tool_use() {
        let app = App::default();

        let response = Response::new("Assistant response")
            .tool_use(vec![])
            .finish_reason(FinishReason::EndTurn);

        let (app, command) = app.run(response).unwrap();

        assert!(app.tool_use_part.is_empty());
        assert!(command.has(ChatResponse::Text("Assistant response".to_string())));
    }

    #[test]

    fn test_tool_use_seq() {
        let app = App::default();

        let message_1 = Action::AssistantResponse(
            Response::new("Let's use foo tool").add_tool_use(
                ToolUsePart::default()
                    .name(ToolName::new("foo"))
                    .arguments_part(r#"{"foo": 1,"#)
                    .use_id(ToolUseId::new("tool_use_001")),
            ),
        );

        let message_2 = Action::AssistantResponse(
            Response::new("")
                .add_tool_use(ToolUsePart::default().arguments_part(r#""bar": 2}"#))
                .finish_reason(FinishReason::ToolUse),
        );

        let message_3 = Action::ToolResponse(
            ToolResult::new(ToolName::new("foo")).content(json!({"a": 100, "b": 200})),
        );

        // LLM made a tool_use request
        let (app, _) = app.run_seq(vec![message_1, message_2, message_3]).unwrap();

        assert_eq!(
            app.request.messages[0],
            ChatMessage::assistant("Let's use foo tool")
                .tool_use(
                    ToolUse::new(ToolName::new("foo"))
                        .arguments(json!({"foo": 1, "bar": 2}))
                        .use_id(ToolUseId::new("tool_use_001"))
                )
                .into()
        );
    }

    #[test]
    fn test_tool_result_seq() {
        let app = App::default();

        let message_1 = Action::AssistantResponse(
            Response::new("Let's use foo tool")
                .add_tool_use(
                    ToolUsePart::default()
                        .name(ToolName::new("foo"))
                        .arguments_part(r#"{"foo": 1, "bar": 2}"#)
                        .use_id(ToolUseId::new("tool_use_001")),
                )
                .finish_reason(FinishReason::ToolUse),
        );

        let tool_result =
            ToolResult::new(ToolName::new("foo")).content(json!({"a": 100, "b": 200}));
        let message_2 = Action::ToolResponse(tool_result.clone());

        let (app, _) = app.run_seq(vec![message_1, message_2]).unwrap();

        assert_eq!(
            app.request.messages,
            vec![
                ChatMessage::assistant("Let's use foo tool")
                    .tool_use(
                        ToolUse::new(ToolName::new("foo"))
                            .arguments(json!({"foo": 1, "bar": 2}))
                            .use_id(ToolUseId::new("tool_use_001"))
                    )
                    .into(),
                RequestMessage::from(tool_result)
            ],
        );
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
}
