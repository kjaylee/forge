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
    use tempfile::TempDir;

    use crate::ToolCallService;

    pub struct Fixture {
        _temp_dir: TempDir,
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

        pub async fn setup<F, Fut>(creator: F) -> Self
        where
            F: Fn(TempDir) -> Fut,
            Fut: std::future::Future<Output = TempDir>,
        {
            let temp_dir = TempDir::new().unwrap();
            let temp_dir = creator(temp_dir).await;
            Self { _temp_dir: temp_dir }
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
