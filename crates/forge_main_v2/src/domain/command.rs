pub enum Command {
    New,
    Message(String),
    Info,
    Exit,
    Models,
    Dump,
    Custom(CommandPayload),
}

pub struct CommandPayload {
    pub name: String,
    pub value: Option<String>,
}

// Command definition struct for registration
#[derive(Clone)]
pub struct CommandDefinition {
    pub name: String,
    pub description: String,
    pub value: Option<String>,
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_command_variants() {
        // Test the Message variant
        let message_cmd = Command::Message(String::from("Hello world"));
        match message_cmd {
            Command::Message(text) => assert_eq!(text, "Hello world"),
            _ => panic!("Should be a message command"),
        }

        // Test the Custom variant
        let custom_payload = CommandPayload {
            name: String::from("test"),
            value: Some(String::from("value")),
        };
        let custom_cmd = Command::Custom(custom_payload);
        match custom_cmd {
            Command::Custom(payload) => {
                assert_eq!(payload.name, "test");
                assert_eq!(payload.value, Some(String::from("value")));
            }
            _ => panic!("Should be a custom command"),
        }
    }
}
