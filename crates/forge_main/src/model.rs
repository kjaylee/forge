use std::collections::BTreeMap;

use anyhow::Result;
use colored::Colorize;
use forge_domain::Model;

use crate::console::CONSOLE;

pub fn display_models(models: &[Model]) -> Result<()> {
    CONSOLE.newline()?;

    // Group models by provider
    let mut models_by_provider: BTreeMap<String, Vec<&Model>> = BTreeMap::new();
    for model in models {
        let provider = model
            .id
            .as_str()
            .split('/')
            .next()
            .unwrap_or("unknown")
            .to_string();
        models_by_provider.entry(provider).or_default().push(model);
    }

    // Display models grouped by provider
    for (_, provider_models) in models_by_provider.iter() {
        for model in provider_models {
            CONSOLE.writeln(format!(
                "  {}: {}({})",
                model.id.to_string().yellow(),
                model.name,
                model.context_length,
            ))?;
        }
        CONSOLE.newline()?;
    }

    Ok(())
}
