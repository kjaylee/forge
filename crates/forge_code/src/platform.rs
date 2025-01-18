use forge_domain::CodeInfo;

pub enum Platforms {
    #[cfg(unix)]
    Unix(crate::unix::UnixCodeInfo),
}

impl CodeInfo for Platforms {
    fn vs_code_path(&self) -> Option<Vec<String>> {
        match self {
            #[cfg(unix)]
            Platforms::Unix(info) => info.vs_code_path(),
        }
    }

    fn is_running(&self) -> bool {
        match self {
            #[cfg(unix)]
            Platforms::Unix(info) => info.is_running(),
        }
    }
}

impl Default for Platforms {
    fn default() -> Self {
        #[cfg(unix)]
        return Platforms::Unix(crate::unix::UnixCodeInfo);
    }
}
