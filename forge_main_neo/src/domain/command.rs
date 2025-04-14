#[derive(Default)]
pub struct CommandList {
    commands: Vec<Command>,
}

impl CommandList {
    pub fn insert(&mut self, command: Command) {
        self.commands.push(command);
    }

    pub fn into_inner(self) -> Vec<Command> {
        self.commands
    }

    pub fn dispatch_user_message(&mut self, message: String) {
        self.insert(Command::UserMessage(message));
    }

    pub fn dispatch_exit(&mut self) {
        self.insert(Command::Exit);
    }
}

#[derive(Debug)]
pub enum Command {
    Suspend,
    ToggleMode(String),
    UserMessage(String),
    Exit,
    Empty,
}
