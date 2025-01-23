use std::collections::HashMap;
use std::path::PathBuf;
use once_cell::sync::OnceCell;
use crate::language::LanguageSyntaxConfig;
use crate::languages::RUST_CONFIG;

pub struct LanguageRegistry {
    configs: HashMap<String, &'static LanguageSyntaxConfig>,
}

impl LanguageRegistry {
    pub fn global() -> &'static LanguageRegistry {
        static INSTANCE: OnceCell<LanguageRegistry> = OnceCell::new();
        INSTANCE.get_or_init(|| {
            let mut registry = LanguageRegistry {
                configs: HashMap::new(),
            };
            registry.register_defaults();
            registry
        })
    }

    pub fn register(&mut self, config: &'static LanguageSyntaxConfig) {
        self.configs.insert(config.language_str.clone(), config);
    }

    fn register_defaults(&mut self) {
        // Register Rust language support
        self.register(&RUST_CONFIG);
    }

    pub fn get_by_extension(&self, ext: &str) -> Option<&'static LanguageSyntaxConfig> {
        self.configs.values()
            .find(|config| config.file_extensions.contains(&ext))
            .copied()
    }

    pub fn get_by_language_id(&self, id: &str) -> Option<&'static LanguageSyntaxConfig> {
        self.configs.values()
            .find(|config| config.language_ids.contains(&id))
            .copied()
    }

    pub fn get_by_name(&self, name: &str) -> Option<&'static LanguageSyntaxConfig> {
        self.configs.get(name).copied()
    }
    pub fn for_file_path(&self, file_path: &str) -> Option<&LanguageSyntaxConfig> {
        let file_path = PathBuf::from(file_path);
        let file_extension = file_path
            .extension()
            .map(|extension| extension.to_str())
            .map(|extension| extension.to_owned())
            .flatten();
        match file_extension {
            Some(extension) => self
                .get_by_extension(&extension)
                .or_else(|| self.get_by_name(&extension)),
            None => None,
        }
    }
}