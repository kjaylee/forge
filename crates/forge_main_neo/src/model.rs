#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use crate::command::Command;

    #[test]
    fn test_command_and_with_two_commands() {
        let fixture = Command::Empty.and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_chaining() {
        let fixture = Command::Empty
            .and(Command::Exit)
            .and(Command::ReadWorkspace);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit, Command::ReadWorkspace]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_with_existing_and() {
        let fixture = Command::And(vec![Command::Empty]).and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_complex_chaining() {
        let fixture = Command::SendMessage("hello".to_string())
            .and(Command::ReadWorkspace)
            .and(Command::Empty)
            .and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::SendMessage("hello".to_string()),
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }
}
