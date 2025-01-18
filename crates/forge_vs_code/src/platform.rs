use forge_domain::CodeInfo;

pub enum Platforms {
    #[cfg(target_os = "linux")]
    Linux(crate::linux::LinuxCodeInfo),
    #[cfg(target_os = "macos")]
    Macos(crate::macos::MacOsCodeInfo),
}

impl CodeInfo for Platforms {
    fn hash_path(&self, folder_path: &str, try_ceil: bool) -> anyhow::Result<String> {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.hash_path(folder_path, try_ceil),
            #[cfg(target_os = "macos")]
            Platforms::Macos(info) => info.hash_path(folder_path, try_ceil),
        }
    }

    fn vs_code_path(&self) -> Option<String> {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.vs_code_path(),
            #[cfg(target_os = "macos")]
            Platforms::Macos(info) => info.vs_code_path(),
        }
    }

    fn is_running(&self) -> bool {
        match self {
            #[cfg(target_os = "linux")]
            Platforms::Linux(info) => info.is_running(),
            #[cfg(target_os = "macos")]
            Platforms::Macos(info) => info.is_running(),
        }
    }
}

impl Default for Platforms {
    fn default() -> Self {
        #[cfg(target_os = "linux")]
        return Platforms::Linux(crate::linux::LinuxCodeInfo);
        #[cfg(target_os = "macos")]
        return Platforms::Macos(crate::macos::MacOsCodeInfo);
    }
}
