# Error Handling FAQ

[Previous content up to Error Types section...]

### Q: When should I use anyhow::Error vs custom domain errors?
A: The choice between anyhow::Error and custom domain errors depends on your use case:

Use **anyhow::Error** when:
1. Writing small applications or tools
2. Creating quick prototypes
3. Building short-lived scripts
4. The errors don't need to be handled programmatically (just displayed or logged)

```rust
// Example using anyhow
use anyhow::{Context, Result};

fn quick_tool() -> Result<()> {
    let config = std::fs::read_to_string("config.json")
        .context("failed to read config")?;
    let data: Value = serde_json::from_str(&config)
        .context("failed to parse config")?;
    // ... more code ...
    Ok(())
}
```

Use **custom domain errors** (with thiserror) when:
1. Building libraries or reusable components
2. Creating long-lived applications
3. Errors need to be handled programmatically
4. You need to provide a stable error handling API
5. Different error cases need different handling

```rust
// Example using custom domain errors
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ConfigError {
    #[error("failed to read config file: {0}")]
    FileRead(#[from] std::io::Error),
    
    #[error("invalid config format: {0}")]
    Format(#[from] serde_json::Error),
    
    #[error("missing required field: {0}")]
    MissingField(String),
}

fn process_config() -> Result<Config, ConfigError> {
    let content = std::fs::read_to_string("config.json")?;
    let config: Value = serde_json::from_str(&content)?;
    
    if config["required_field"].is_null() {
        return Err(ConfigError::MissingField("required_field".into()));
    }
    
    // ... more validation ...
    Ok(Config { /* ... */ })
}

// Caller can handle specific error cases
match process_config() {
    Err(ConfigError::MissingField(field)) => {
        // Handle missing field specifically
    }
    Err(ConfigError::Format(_)) => {
        // Handle format errors differently
    }
    Ok(config) => {
        // Use config
    }
}
```

Remember:
- anyhow is for cases where you just want to propagate and display errors
- thiserror is for cases where you need to define an error handling API
- You can use both in the same application (thiserror for libraries/core modules, anyhow for application code)
- Prefer custom domain errors when in doubt, as you can always add more error handling capabilities later

[Rest of the previous content...]