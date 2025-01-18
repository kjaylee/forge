pub trait ActiveFiles {
    fn active_files(&self) -> anyhow::Result<Vec<String>>;
}
