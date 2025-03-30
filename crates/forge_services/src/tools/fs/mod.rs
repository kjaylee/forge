mod file_info;
mod fs_find;
mod fs_list;
mod fs_read;
mod fs_remove;
mod fs_write;

pub use file_info::*;
pub use fs_find::*;
pub use fs_list::*;
pub use fs_read::*;
pub use fs_remove::*;
pub use fs_write::*;

use crate::infra::EnvironmentService;

/// Formats a path for display, converting absolute paths to relative when
/// possible.
///
/// If the path starts with the current working directory, returns a relative
/// path. Otherwise, returns the original absolute path.
pub fn format_display_path<E: EnvironmentService>(
    env_service: &E,
    path: &std::path::Path,
) -> anyhow::Result<String> {
    // Get the current working directory
    let env = env_service.get_environment();
    let cwd = env.cwd.as_path();

    // Try to create a relative path for display if possible
    let display_path = if path.starts_with(cwd) {
        match path.strip_prefix(cwd) {
            Ok(rel_path) => rel_path.display().to_string(),
            Err(_) => path.display().to_string(),
        }
    } else {
        path.display().to_string()
    };

    Ok(display_path)
}
