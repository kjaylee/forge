use crate::context::ContextMessage;
use crate::conversation::Conversation;
use forge_template::Element;
use serde_json::to_string_pretty;

pub fn render_conversation_html(conversation: &Conversation) -> String {
    let html = Element::new("html")
        .attr("lang", "en")
        .append(
            Element::new("head")
                .append(Element::new("meta").attr("charset", "UTF-8"))
                .append(
                    Element::new("meta")
                        .attr("name", "viewport")
                        .attr("content", "width=device-width, initial-scale=1.0"),
                )
                .append(Element::new("title").text(format!("Conversation: {}", conversation.id)))
                .append(Element::new("style").text(include_str!("conversation_style.css"))),
        )
        .append(
            Element::new("body")
                .append(Element::new("h1").text("Conversation"))
                // Basic Information Section
                .append(
                    Element::new("div.section")
                        .append(Element::new("h2").text("Basic Information"))
                        .append(Element::new("p").text(format!("ID: {}", conversation.id)))
                        .append(
                            Element::new("p").text(format!("Archived: {}", conversation.archived)),
                        ),
                )
                // Variables Section
                .append(create_variables_section(conversation))
                // Agents Section
                .append(create_agents_section(conversation))
                // Events Section
                .append(create_events_section(conversation))
                // Agent States Section
                .append(create_agent_states_section(conversation)),
        );

    html.render()
}

fn create_variables_section(conversation: &Conversation) -> Element {
    let mut section = Element::new("div.section")
        .append(Element::new("h2").text("Variables"))
        .append(
            Element::new("table").append(
                Element::new("tr")
                    .append(Element::new("th").text("Key"))
                    .append(Element::new("th").text("Value")),
            ),
        );

    let table = section.children.last_mut().unwrap();

    for (key, value) in &conversation.variables {
        table.children.push(
            Element::new("tr")
                .append(Element::new("td").text(key))
                .append(Element::new("td").append(Element::new("pre").text(value.to_string()))),
        );
    }

    section
}

fn create_agents_section(conversation: &Conversation) -> Element {
    let mut section = Element::new("div.section").append(Element::new("h2").text("Agents"));

    for agent in &conversation.agents {
        let mut agent_div = Element::new("div.agent")
            .append(Element::new("div.agent-header").append(Element::new("h3").text(&agent.id)));

        // Add model if available
        if let Some(model) = &agent.model {
            let header = agent_div.children.last_mut().unwrap();
            header
                .children
                .push(Element::new("span").text(format!("Model: {}", model)));
        }

        // Add custom rules if available
        if let Some(custom_rules) = &agent.custom_rules {
            agent_div.children.push(
                Element::new("div")
                    .append(Element::new("h4").text("Custom Rules"))
                    .append(Element::new("pre").text(custom_rules)),
            );
        }

        // Add description if available
        if let Some(description) = &agent.description {
            agent_div.children.push(
                Element::new("div")
                    .append(Element::new("h4").text("Description"))
                    .append(Element::new("p").text(description)),
            );
        }

        // Add subscriptions if available
        if let Some(subscriptions) = &agent.subscribe {
            if !subscriptions.is_empty() {
                let mut subscriptions_div = Element::new("div")
                    .append(Element::new("h4").text("Subscriptions"))
                    .append(Element::new("ul"));

                let ul = subscriptions_div.children.last_mut().unwrap();
                for subscription in subscriptions {
                    ul.children.push(Element::new("li").text(subscription));
                }

                agent_div.children.push(subscriptions_div);
            }
        }

        // Add temperature if available
        if let Some(temperature) = &agent.temperature {
            agent_div
                .children
                .push(Element::new("p").text(format!("Temperature: {}", temperature)));
        }

        // Add max turns if available
        if let Some(max_turns) = agent.max_turns {
            agent_div
                .children
                .push(Element::new("p").text(format!("Max Turns: {}", max_turns)));
        }

        // Add max walker depth if available
        if let Some(max_walker_depth) = agent.max_walker_depth {
            agent_div
                .children
                .push(Element::new("p").text(format!("Max Walker Depth: {}", max_walker_depth)));
        }

        section.children.push(agent_div);
    }

    section
}

fn create_events_section(conversation: &Conversation) -> Element {
    let mut section = Element::new("div.section").append(Element::new("h2").text("Events"));

    for event in &conversation.events {
        let event_div = Element::new("div.event")
            .append(
                Element::new("div.event-header")
                    .append(Element::new("h3").text(&event.name))
                    .append(Element::new("span").text(format!("ID: {}", event.id))),
            )
            .append(
                Element::new("div")
                    .append(Element::new("h4").text("Value"))
                    .append(Element::new("pre").text(&event.value)),
            )
            .append(
                Element::new("div")
                    .append(Element::new("h4").text("Timestamp"))
                    .append(Element::new("pre").text(format!("{}", event.timestamp))),
            );

        section.children.push(event_div);
    }

    section
}

fn create_agent_states_section(conversation: &Conversation) -> Element {
    let mut section = Element::new("div.section").append(Element::new("h2").text("Agent States"));

    for (agent_id, state) in &conversation.state {
        let mut agent_div = Element::new("div.agent").append(Element::new("h3").text(agent_id));

        // Add context if available
        if let Some(context) = &state.context {
            let mut context_div = Element::new("div")
                .append(Element::new("h4").text("Context"))
                .append(
                    Element::new("div.context-section").append(Element::new("h5").text("Messages")),
                );

            let context_section = context_div.children.last_mut().unwrap();

            // Add messages
            for message in &context.messages {
                match message {
                    ContextMessage::ContentMessage(content_message) => {
                        // Convert role to lowercase for the class
                        let role_lowercase = content_message.role.to_string().to_lowercase();

                        let mut message_div = Element::new(format!(
                            "details.message-card.message-{}",
                            role_lowercase
                        ))
                        .append(
                            Element::new("summary")
                                .text(format!("{} Message", content_message.role)),
                        )
                        .append(Element::new("pre").text(&content_message.content));

                        // Add tool calls if any
                        if let Some(tool_calls) = &content_message.tool_calls {
                            if !tool_calls.is_empty() {
                                let mut tool_calls_div = Element::new("div")
                                    .append(Element::new("h6").text("Tool Calls"));

                                for tool_call in tool_calls {
                                    let mut call_div = Element::new("div.tool-call").append(
                                        Element::new("p")
                                            .append(Element::new("strong").text("Name: "))
                                            .text(tool_call.name.as_str()),
                                    );

                                    // Add call_id if available
                                    if let Some(call_id) = &tool_call.call_id {
                                        call_div.children.push(
                                            Element::new("p")
                                                .append(Element::new("strong").text("ID: "))
                                                .text(call_id.as_str()),
                                        );
                                    }

                                    // Add arguments
                                    call_div.children.push(
                                        Element::new("p")
                                            .append(Element::new("strong").text("Arguments: ")),
                                    );
                                    call_div.children.push(Element::new("pre").text(
                                        to_string_pretty(&tool_call.arguments).unwrap_or_default(),
                                    ));

                                    tool_calls_div.children.push(call_div);
                                }

                                message_div.children.push(tool_calls_div);
                            }
                        }

                        context_section.children.push(message_div);
                    }
                    ContextMessage::ToolMessage(tool_result) => {
                        // Tool Message
                        let tool_div = Element::new("div.message-card.message-tool")
                            .append(Element::new("h5").text("Tool Result"))
                            .append(
                                Element::new("div.tool-result")
                                    .append(
                                        Element::new("p")
                                            .append(Element::new("strong").text("Tool Name: "))
                                            .text(tool_result.name.as_str()),
                                    )
                                    .append(Element::new("pre").text(
                                        to_string_pretty(&tool_result.content).unwrap_or_default(),
                                    )),
                            );

                        context_section.children.push(tool_div);
                    }
                    ContextMessage::Image(url) => {
                        // Image message
                        let image_div = Element::new("div.message-card.message-user")
                            .append(Element::new("h5").text("Image Attachment"))
                            .append(Element::new("p").text(format!("URL: {}", url)));

                        context_section.children.push(image_div);
                    }
                }
            }

            // Add Tools section
            let tools_section = Element::new("h5").text("Tools");
            context_section.children.push(tools_section);

            let tools_div = Element::new("div");
            context_section.children.push(tools_div);

            for tool in &context.tools {
                // Use input_schema instead of parameters
                let mut tool_div = Element::new("div.tool-call")
                    .append(
                        Element::new("p")
                            .append(Element::new("strong").text("Tool: "))
                            .text(tool.name.as_str()),
                    )
                    .append(
                        Element::new("p")
                            .append(Element::new("strong").text("Description: "))
                            .text(&tool.description),
                    );

                // Display the input schema
                tool_div
                    .children
                    .push(Element::new("p").append(Element::new("strong").text("Input Schema: ")));
                tool_div.children.push(
                    Element::new("pre")
                        .text(to_string_pretty(&tool.input_schema).unwrap_or_default()),
                );

                // If output schema exists, display it too
                if let Some(output_schema) = &tool.output_schema {
                    tool_div.children.push(
                        Element::new("p").append(Element::new("strong").text("Output Schema: ")),
                    );
                    tool_div.children.push(
                        Element::new("pre")
                            .text(to_string_pretty(output_schema).unwrap_or_default()),
                    );
                }

                context_section
                    .children
                    .last_mut()
                    .unwrap()
                    .children
                    .push(tool_div);
            }

            // Add Tool Choice if available
            if let Some(tool_choice) = &context.tool_choice {
                context_section
                    .children
                    .push(Element::new("h5").text("Tool Choice"));
                context_section
                    .children
                    .push(Element::new("div.tool-choice").append(
                        Element::new("pre").text(to_string_pretty(tool_choice).unwrap_or_default()),
                    ));
            }

            // Add Max Tokens if available
            if let Some(max_tokens) = context.max_tokens {
                context_section.children.push(
                    Element::new("p")
                        .append(Element::new("strong").text("Max Tokens: "))
                        .text(format!("{}", max_tokens)),
                );
            }

            // Add Temperature if available
            if let Some(temperature) = context.temperature {
                context_section.children.push(
                    Element::new("p")
                        .append(Element::new("strong").text("Temperature: "))
                        .text(format!("{}", temperature)),
                );
            }

            agent_div.children.push(context_div);
        }

        // Add event queue
        let mut event_queue_div = Element::new("div")
            .append(Element::new("h4").text("Event Queue"))
            .append(Element::new("ul"));

        let ul = event_queue_div.children.last_mut().unwrap();
        for event in &state.queue {
            ul.children
                .push(Element::new("li").text(format!("{} (ID: {})", event.name, event.id)));
        }

        agent_div.children.push(event_queue_div);
        section.children.push(agent_div);
    }

    section
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conversation::Conversation;

    #[test]
    fn test_render_empty_conversation() {
        // Create a new empty conversation
        let id = crate::conversation::ConversationId::generate();
        let workflow = crate::Workflow {
            agents: Vec::new(),
            variables: std::collections::HashMap::new(),
            commands: Vec::new(),
            model: None,
            max_walker_depth: None,
            custom_rules: None,
            temperature: None,
        };

        let fixture = Conversation::new(id, workflow);
        let actual = render_conversation_html(&fixture);

        // We're verifying that the function runs without errors
        // and returns a non-empty string for an empty conversation
        assert!(actual.contains("<html"));
        assert!(actual.contains("</html>"));
        assert!(actual.contains("Conversation: "));
        assert!(actual.contains("Basic Information"));
        assert!(actual.contains("Variables"));
        assert!(actual.contains("Agents"));
        assert!(actual.contains("Events"));
        assert!(actual.contains("Agent States"));
    }
}
