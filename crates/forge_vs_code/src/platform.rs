use forge_domain::CodeInfo;

pub enum Platforms {
    #[cfg(target_os = "linux")]
    Linux(crate::linux::LinuxCodeInfo),
}

impl CodeInfo for Platforms {
    fn hash_path(&self, folder_path: &str) -> anyhow::Result<String> {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.hash_path(folder_path),
        }
    }

    fn vs_code_path(&self) -> Option<String> {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.vs_code_path(),
        }
    }

    fn is_running(&self) -> bool {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.is_running(),
        }
    }
}

impl Default for Platforms {
    fn default() -> Self {
        #[cfg(target_os = "linux")]
        return Platforms::Linux(crate::linux::LinuxCodeInfo);
    }
}
