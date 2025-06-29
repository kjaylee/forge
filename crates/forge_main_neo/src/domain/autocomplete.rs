/// Represents an individual autocomplete command option
#[derive(Clone, Debug, PartialEq)]
pub struct AutocompleteOption {
    pub name: String,
    pub description: String,
}

impl AutocompleteOption {
    pub fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self { name: name.into(), description: description.into() }
    }
}
