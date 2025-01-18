use forge_domain::ActiveFiles;
use forge_vs_code::ForgeVsCode;

pub struct ForgeAllIdes {
    ides: Vec<IDEs>,
}

enum IDEs {
    VsCode(ForgeVsCode),
}

impl ForgeAllIdes {
    pub fn new<T: ToString>(cwd: T) -> Self {
        let ides: Vec<IDEs> = vec![IDEs::VsCode(ForgeVsCode::from(cwd.to_string()))];
        Self { ides }
    }
}

impl ActiveFiles for ForgeAllIdes {
    fn active_files(&self) -> anyhow::Result<Vec<String>> {
        let mut files = vec!["The active files are:".to_string()];
        for ide in &self.ides {
            if let Ok(ide_files) = ide.active_files() {
                files.extend(ide_files);
            }
        }
        Ok(files)
    }
}

impl ActiveFiles for IDEs {
    fn active_files(&self) -> anyhow::Result<Vec<String>> {
        match self {
            IDEs::VsCode(ide) => ide.active_files(),
        }
    }
}
