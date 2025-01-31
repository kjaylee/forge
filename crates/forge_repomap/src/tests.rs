#[cfg(test)]
mod git_tests {
    use std::path::PathBuf;
    use crate::{GitWalker};
    use insta;

    #[tokio::test]
    async fn test_git_walker_reads_files() {
        // Get the current crate's root directory
        let root_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        
        // Try reading files
        let walker = GitWalker{};
        let files = walker.read_files(&root_path).await.unwrap();
        
        // Create a sorted list of file paths for snapshot
        let mut paths: Vec<_> = files.keys().collect();
        paths.sort();
        
        insta::assert_snapshot!(format!("{:#?}", paths));
    }
}

mod repomap_tests {
    use std::path::PathBuf;
    use crate::{RepoMap, SymbolIndex, GitWalker};
    use insta;

    #[tokio::test]
    async fn test_create_repomap_for_self() {
        let root_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        
        let walker = GitWalker{};
        let files = walker.read_files(&root_path).await.unwrap();
        let mut symbol_index = SymbolIndex::new(&root_path);
        symbol_index.generate_from_files(files).await;
        assert!(!symbol_index.definitions().is_empty(), "No definitions found in the repository");
        let repo_map = RepoMap::new()
            .with_map_tokens(2048); 
        
        let map = repo_map.get_repo_map(&symbol_index).await.unwrap();
        
        assert!(!map.is_empty(), "Generated repository map is empty");
        
        insta::assert_snapshot!(map);
    }
}
