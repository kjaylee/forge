use forge_code::Code;
use forge_domain::{Ide, IdeRepository, Workspace, WorkspaceId};

pub struct ForgeAllIdes {
    ides: Vec<IDEs>,
}

enum IDEs {
    VsCode(Code),
}

impl ForgeAllIdes {
    pub fn new<T: ToString>(cwd: T) -> Self {
        let ides: Vec<IDEs> = vec![IDEs::VsCode(Code::new(cwd.to_string()))];
        Self { ides }
    }
}

#[async_trait::async_trait]
impl IdeRepository for ForgeAllIdes {
    async fn get_active_ides(&self) -> anyhow::Result<Vec<Ide>> {
        let mut files = vec![];
        for ide in &self.ides {
            if let Ok(ide_files) = ide.get_active_ides().await {
                files.extend(ide_files);
            }
        }

        Ok(files)
    }

    async fn get_workspace(&self, ide: &WorkspaceId) -> anyhow::Result<Workspace> {
        for i in &self.ides {
            if let Ok(workspace) = i.get_workspace(ide).await {
                return Ok(workspace);
            }
        }

        anyhow::bail!("IDE not found")
    }
}

#[async_trait::async_trait]
impl IdeRepository for IDEs {
    async fn get_active_ides(&self) -> anyhow::Result<Vec<Ide>> {
        match self {
            IDEs::VsCode(ide) => ide.get_active_ides().await,
        }
    }

    async fn get_workspace(&self, ide: &WorkspaceId) -> anyhow::Result<Workspace> {
        match self {
            IDEs::VsCode(code) => code.get_workspace(ide).await,
        }
    }
}
