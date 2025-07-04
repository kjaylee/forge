use serde::{Deserialize, Serialize};

/// Represents a reasoning detail that may be included in the response
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq)]
pub struct ReasoningPart {
    pub text: Option<String>,
    pub signature: Option<String>,
}

/// Represents a reasoning detail that may be included in the response
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq)]
pub struct ReasoningFull {
    pub text: Option<String>,
    pub signature: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Reasoning {
    Part(Vec<ReasoningPart>),
    Full(Vec<ReasoningFull>),
}

impl Reasoning {
    pub fn as_partial(&self) -> Option<&Vec<ReasoningPart>> {
        match self {
            Reasoning::Part(parts) => Some(parts),
            Reasoning::Full(_) => None,
        }
    }

    pub fn as_full(&self) -> Option<&Vec<ReasoningFull>> {
        match self {
            Reasoning::Part(_) => None,
            Reasoning::Full(full) => Some(full),
        }
    }

    pub fn from_parts(parts: Vec<Vec<ReasoningPart>>) -> Vec<ReasoningFull> {
        // We merge based on index.
        // eg. [ [a,b,c], [d,e,f], [g,h,i] ] -> [a,d,g], [b,e,h], [c,f,i]

        // Find the maximum length of the inner vectors
        let max_length = parts.iter().map(|v| v.len()).max().unwrap_or(0);

        // For each index, collect all parts at that index
        (0..max_length)
            .map(|i| {
                let mut merged = ReasoningFull { text: None, signature: None };

                // Go through each part vector and get the element at the current index if it exists
                for part_vec in &parts {
                    if i < part_vec.len() {
                        let part = &part_vec[i];

                        // Merge the text
                        if let Some(text) = &part.text {
                            match &mut merged.text {
                                Some(merged_text) => merged_text.push_str(text),
                                None => merged.text = Some(text.clone()),
                            }
                        }

                        // Merge the signature
                        if let Some(signature) = &part.signature {
                            match &mut merged.signature {
                                Some(merged_signature) => merged_signature.push_str(signature),
                                None => merged.signature = Some(signature.clone()),
                            }
                        }
                    }
                }

                merged
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reasoning_detail_from_parts() {
        // Create a fixture with three vectors of ReasoningDetailPart
        let fixture = vec![
            // First vector [a, b, c]
            vec![
                ReasoningPart {
                    text: Some("a-text".to_string()),
                    signature: Some("a-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("b-text".to_string()),
                    signature: Some("b-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("c-text".to_string()),
                    signature: Some("c-sig".to_string()),
                },
            ],
            // Second vector [d, e, f]
            vec![
                ReasoningPart {
                    text: Some("d-text".to_string()),
                    signature: Some("d-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("e-text".to_string()),
                    signature: Some("e-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("f-text".to_string()),
                    signature: Some("f-sig".to_string()),
                },
            ],
            // Third vector [g, h, i]
            vec![
                ReasoningPart {
                    text: Some("g-text".to_string()),
                    signature: Some("g-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("h-text".to_string()),
                    signature: Some("h-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("i-text".to_string()),
                    signature: Some("i-sig".to_string()),
                },
            ],
        ];

        // Execute the function to get the actual result
        let actual = Reasoning::from_parts(fixture);

        // Define the expected result
        let expected = vec![
            // First merged vector [a, d, g]
            ReasoningFull {
                text: Some("a-textd-textg-text".to_string()),
                signature: Some("a-sigd-sigg-sig".to_string()),
            },
            // Second merged vector [b, e, h]
            ReasoningFull {
                text: Some("b-texte-texth-text".to_string()),
                signature: Some("b-sige-sigh-sig".to_string()),
            },
            // Third merged vector [c, f, i]
            ReasoningFull {
                text: Some("c-textf-texti-text".to_string()),
                signature: Some("c-sigf-sigi-sig".to_string()),
            },
        ];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_parts_with_different_lengths() {
        // Create a fixture with vectors of different lengths
        let fixture = vec![
            vec![
                ReasoningPart {
                    text: Some("a-text".to_string()),
                    signature: Some("a-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("b-text".to_string()),
                    signature: Some("b-sig".to_string()),
                },
            ],
            vec![ReasoningPart {
                text: Some("c-text".to_string()),
                signature: Some("c-sig".to_string()),
            }],
            vec![
                ReasoningPart {
                    text: Some("d-text".to_string()),
                    signature: Some("d-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("e-text".to_string()),
                    signature: Some("e-sig".to_string()),
                },
                ReasoningPart {
                    text: Some("f-text".to_string()),
                    signature: Some("f-sig".to_string()),
                },
            ],
        ];

        // Execute the function to get the actual result
        let actual = Reasoning::from_parts(fixture);

        // Define the expected result
        let expected = vec![
            // First merged vector [a, c, d]
            ReasoningFull {
                text: Some("a-textc-textd-text".to_string()),
                signature: Some("a-sigc-sigd-sig".to_string()),
            },
            // Second merged vector [b, e]
            ReasoningFull {
                text: Some("b-texte-text".to_string()),
                signature: Some("b-sige-sig".to_string()),
            },
            // Third merged vector [f]
            ReasoningFull {
                text: Some("f-text".to_string()),
                signature: Some("f-sig".to_string()),
            },
        ];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_parts_with_none_values() {
        // Create a fixture with some None values
        let fixture = vec![
            vec![ReasoningPart { text: Some("a-text".to_string()), signature: None }],
            vec![ReasoningPart { text: None, signature: Some("b-sig".to_string()) }],
        ];

        // Execute the function to get the actual result
        let actual = Reasoning::from_parts(fixture);

        // Define the expected result
        let expected = vec![ReasoningFull {
            text: Some("a-text".to_string()),
            signature: Some("b-sig".to_string()),
        }];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_empty_parts() {
        // Empty fixture
        let fixture: Vec<Vec<ReasoningPart>> = vec![];

        // Execute the function to get the actual result
        let actual = Reasoning::from_parts(fixture);

        // Define the expected result - should be an empty vector
        let expected: Vec<ReasoningFull> = vec![];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }
}
