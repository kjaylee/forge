use forge_services::ConsoleService;

pub struct ForgeConsoleService;

#[async_trait::async_trait]
impl ConsoleService for ForgeConsoleService {
    async fn print(&self, output: &str) -> anyhow::Result<()> {
        print!("{}", output);
        Ok(())
    }
}
