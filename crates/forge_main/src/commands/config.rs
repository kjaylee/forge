use std::collections::HashMap;
use std::fs;

use anyhow::Result;
use forge_display::TitleFormat;
use forge_domain::ForgeConfig;

use crate::console::CONSOLE;

/// Command handler for /set-coding-model
pub fn handle_set_coding_model(model_name: &str) -> Result<()> {
    update_forge_file_model("coding", model_name)
}

/// Command handler for /set-summarization-model
pub fn handle_set_summarization_model(model_name: &str) -> Result<()> {
    update_forge_file_model("summarization", model_name)
}

/// Command handler for /set-default-model
pub fn handle_set_default_model(model_name: &str) -> Result<()> {
    update_forge_file_model("default", model_name)
}

/// Helper function to update a model in the .forge file
fn update_forge_file_model(model_type: &str, model_name: &str) -> Result<()> {
    // Load existing .forge file or create new one
    let mut config = load_forge_config()?;

    // Update the specified model
    let models = config.models.get_or_insert_with(HashMap::new);
    models.insert(model_type.to_string(), model_name.to_string());

    // Save the updated configuration
    save_forge_config(&config)?;

    // Verify file was written
    let current_dir = std::env::current_dir()?;
    let path = current_dir.join(".forge");
    if path.exists() {
        let _ = fs::read_to_string(&path)?;
    } else {
        CONSOLE.write(TitleFormat::failed("Failed to create .forge file").format())?;
    }

    // Use the global CONSOLE instance for output
    CONSOLE.write(
        TitleFormat::success(format!("{} has been set for {}", model_name, model_type)).format(),
    )?;
    Ok(())
}

/// Load configuration from .forge file
pub fn load_forge_config() -> Result<ForgeConfig> {
    // Use absolute path to ensure consistency across components
    let current_dir = std::env::current_dir()?;
    let path = current_dir.join(".forge");

    if !path.exists() {
        // Return empty config if file doesn't exist
        return Ok(ForgeConfig::default());
    }

    let content = fs::read_to_string(&path)?;
    // Parse YAML content
    Ok(serde_yaml::from_str(&content)?)
}

/// Save configuration to .forge file
pub fn save_forge_config(config: &ForgeConfig) -> Result<()> {
    // Use absolute path to ensure consistency across components
    let current_dir = std::env::current_dir()?;
    let path = current_dir.join(".forge");

    // Convert to YAML
    let content = serde_yaml::to_string(config)?;

    // Write to file
    fs::write(&path, &content)?;

    // Verify file exists after write
    if path.exists() {
        Ok(())
    } else {
        Err(anyhow::anyhow!(
            "Failed to write .forge file to {}",
            path.display()
        ))
    }
}

#[cfg(test)]
mod tests {
    use tempfile::TempDir;

    use super::*;

    #[test]
    fn test_forge_file_creation() {
        // Create temp dir for test
        let temp_dir = TempDir::new().unwrap();
        let prev_dir = std::env::current_dir().unwrap();
        std::env::set_current_dir(temp_dir.path()).unwrap();

        // Test file creation
        let model_name = "anthropic/claude-3.5-haiku";
        handle_set_coding_model(model_name).unwrap(); // Mocking the output since we can't redirect CONSOLE in tests
        println!("coding model set to: {}", model_name);

        // Verify file was created with correct content
        let abs_path = std::env::current_dir().unwrap().join(".forge");
        assert!(abs_path.exists());
        let content = fs::read_to_string(abs_path).unwrap();
        let config: ForgeConfig = serde_yaml::from_str(&content).unwrap();

        assert!(config.models.is_some());
        let models = config.models.unwrap();
        assert_eq!(models.get("coding").unwrap(), model_name);

        // Clean up
        std::env::set_current_dir(prev_dir).unwrap();
    }

    #[test]
    fn test_forge_file_update() {
        // Create temp dir for test
        let temp_dir = TempDir::new().unwrap();
        let prev_dir = std::env::current_dir().unwrap();
        std::env::set_current_dir(temp_dir.path()).unwrap();

        // Set initial model
        let initial_model = "anthropic/claude-3.5-haiku";
        handle_set_coding_model(initial_model).unwrap();
        println!("coding model set to: {}", initial_model);

        // Update model
        let updated_model = "anthropic/claude-3.7-sonnet";
        handle_set_coding_model(updated_model).unwrap();
        println!("coding model set to: {}", updated_model);

        // Verify update was applied
        let abs_path = std::env::current_dir().unwrap().join(".forge");
        let content = fs::read_to_string(abs_path).unwrap();
        let config: ForgeConfig = serde_yaml::from_str(&content).unwrap();

        assert!(config.models.is_some());
        let models = config.models.unwrap();
        assert_eq!(models.get("coding").unwrap(), updated_model);

        // Clean up
        std::env::set_current_dir(prev_dir).unwrap();
    }
}
