use crate::*;

#[test]
fn test_auto_compact_transform() {
    // Create a transform that automatically summarizes the context when it exceeds a certain token limit
    let auto_compact_transform = Transform::AutoCompact {
        token_limit: 10000,
    };

    // Create an agent with the transform
    let agent = Agent::new("test_agent")
        .transforms(vec![auto_compact_transform]);

    // Assert that the agent has one transform
    assert_eq!(agent.transforms.as_ref().unwrap().len(), 1);

    // Assert that the transform is the AutoCompact transform
    if let Some(Transform::AutoCompact { token_limit }) = agent.transforms.as_ref().unwrap().first() {
        assert_eq!(*token_limit, 10000);
    } else {
        panic!("Expected AutoCompact transform");
    }
}