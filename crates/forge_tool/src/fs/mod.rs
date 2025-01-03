mod file_info;
mod fs_find;
mod fs_list;
mod fs_read;
mod fs_replace;
mod fs_write;

pub use file_info::*;
pub use fs_find::*;
pub use fs_list::*;
pub use fs_read::*;
pub use fs_replace::*;
pub use fs_write::*;

#[cfg(test)]
pub mod tests {
    use derive_setters::Setters;
    use tempfile::TempDir;

    use crate::ToolCallService;

    #[derive(Setters)]
    pub struct FixtureBuilder {
        _temp_dir: TempDir,
        files: Vec<File>,
        dirs: Vec<String>,
    }

    pub struct File {
        path: String,
        content: String,
    }

    impl File {
        pub fn new(path: impl ToString, content: impl ToString) -> Self {
            Self { path: path.to_string(), content: content.to_string() }
        }
    }

    impl FixtureBuilder {
        pub async fn build(self) -> Fixture {
            // create dirs
            for dir in self.dirs {
                let path = self._temp_dir.path().join(dir);
                tokio::fs::create_dir(path).await.unwrap();
            }
            // create files
            for file in self.files {
                let path = self._temp_dir.path().join(file.path);
                tokio::fs::write(path, file.content).await.unwrap();
            }

            Fixture { _temp_dir: self._temp_dir }
        }
    }

    impl Default for FixtureBuilder {
        fn default() -> Self {
            Self {
                _temp_dir: TempDir::new().unwrap(),
                files: Vec::new(),
                dirs: Vec::new(),
            }
        }
    }

    pub struct Fixture {
        _temp_dir: TempDir,
    }

    impl Default for Fixture {
        fn default() -> Self {
            Self { _temp_dir: TempDir::new().unwrap() }
        }
    }

    impl Fixture {
        pub fn path(&self) -> String {
            self._temp_dir.path().to_string_lossy().to_string()
        }

        pub fn join(&self, path: &str) -> String {
            self._temp_dir
                .path()
                .join(path)
                .to_string_lossy()
                .to_string()
        }

        pub async fn run<R: ToolCallService>(
            &self,
            exec: R,
            input: R::Input,
        ) -> Result<R::Output, String> {
            exec.call(input).await
        }
    }
}
