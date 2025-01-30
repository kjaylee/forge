use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    Granted,
    Denied,
    Prompt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathAccess {
    Read,
    Write,
    ReadWrite,
}

/// A pattern that can match against strings with wildcards
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern(String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct File {
    path: Pattern,
    access: PathAccess,
    status: Status,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Network {
    host: Pattern,
    status: Status,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
    variable: Option<Pattern>,
    status: Status,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Shell {
    shell: String, // sh, bash, zsh, etc. defaults to rbash
    command: Pattern,
    status: Status,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Permissions {
    fs: Vec<File>,
    net: Vec<Network>,
    env: Vec<Env>,
    shell: Vec<Shell>,
}

pub enum Action {
    FileRead { path: PathBuf },
    FileWrite { path: PathBuf },
    Connect { host: String },
    EnvRead { name: String },
    Execute { command: String, path: PathBuf },
}

impl Permissions {
    pub fn validate(&self, action: Action) -> Status {
        todo!()
    }
}
