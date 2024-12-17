use grep::regex::RegexMatcher;
use grep::searcher::sinks::UTF8;
use grep::searcher::SearcherBuilder;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use walkdir::WalkDir;

/// Represents a single search result
#[derive(Debug)]
pub struct SearchResult {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub match_text: String,
    pub before_context: Vec<String>,
    pub after_context: Vec<String>,
}

const MAX_RESULTS: usize = 300;
const CONTEXT_LINES: usize = 1;

/// Executes regex search on a directory
pub fn regex_search_files(
    cwd: &Path,
    directory_path: &Path,
    regex: &str,
    file_pattern: Option<&str>,
) -> io::Result<String> {
    let mut results: Vec<SearchResult> = vec![];
    let matcher = RegexMatcher::new_line_matcher(regex).unwrap();
    let mut searcher = SearcherBuilder::new().line_number(true).build();

    for entry in WalkDir::new(directory_path)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_file())
    {
        let file_path = entry.path();

        // Check for file existence
        if !file_path.exists() {
            eprintln!("Skipping non-existent file: {:?}", file_path);
            continue; // Skip this file but do not fail the function
        }

        // Match file pattern
        if let Some(pattern) = file_pattern {
            if !file_path.to_string_lossy().ends_with(pattern) {
                continue;
            }
        }

        // Validate UTF-8 beforehand to ensure non-UTF8 errors
        let file = File::open(file_path)?;
        let reader = io::BufReader::new(file);
        for line in reader.lines() {
            line?;
        }

        let mut line_context = Vec::new();
        let mut match_count = 0;

        let sink = UTF8(|line_number, line| -> Result<bool, std::io::Error> {
            let column = line.find(regex).unwrap_or(0);

            if match_count >= MAX_RESULTS {
                return Ok(false);
            }

            let result = SearchResult {
                file: file_path.to_string_lossy().to_string(),
                line: line_number as usize,
                column,
                match_text: line.trim_end().to_string(),
                before_context: line_context.clone(),
                after_context: vec![],
            };

            results.push(result);
            if line_context.len() >= CONTEXT_LINES {
                line_context.remove(0); // Maintain fixed-size context buffer
            }
            line_context.push(line.trim_end().to_string());

            match_count += 1;

            Ok(true)
        });

        searcher.search_path(&matcher, file_path, sink)?;
    }

    Ok(format_results(&results, cwd))
}

/// Formats search results into a human-readable string
fn format_results(results: &[SearchResult], cwd: &Path) -> String {
    let mut grouped_results: HashMap<String, Vec<&SearchResult>> = HashMap::new();
    let mut output = String::new();

    if results.len() >= MAX_RESULTS {
        output.push_str(&format!(
            "Showing first {} of {}+ results. Use a more specific search if necessary.\n\n",
            MAX_RESULTS, MAX_RESULTS
        ));
    } else {
        output.push_str(&format!(
            "Found {} result{}.\n\n",
            results.len(),
            if results.len() == 1 { "" } else { "s" }
        ));
    }

    for result in results {
        let relative_path = result
            .file
            .strip_prefix(cwd.to_string_lossy().as_ref())
            .unwrap_or(&result.file);

        grouped_results
            .entry(relative_path.to_string())
            .or_default()
            .push(result);
    }

    for (file, file_results) in grouped_results {
        output.push_str(&format!("{}\n│----\n", file));

        for result in file_results {
            let all_lines: Vec<String> = result
                .before_context
                .iter()
                .chain(std::iter::once(&result.match_text))
                .chain(result.after_context.iter())
                .cloned()
                .collect();

            for line in all_lines {
                output.push_str(&format!("│{}\n", line.trim_end()));
            }

            output.push_str("│----\n");
        }
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::tempdir;

    /// Helper to create files in a directory
    fn create_temp_file(dir: &std::path::Path, name: &str, content: &str) {
        let file_path = dir.join(name);
        let mut file = File::create(file_path).expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write to temp file");
    }

    #[test]
    fn test_empty_directory() {
        let temp_dir = tempdir().unwrap();
        let cwd = temp_dir.path();

        let result = regex_search_files(cwd, temp_dir.path(), "TODO:", None).unwrap();
        assert!(
            result.contains("Found 0 results"),
            "Expected no results in an empty directory."
        );
    }

    #[test]
    fn test_file_with_no_matches() {
        let temp_dir = tempdir().unwrap();
        create_temp_file(temp_dir.path(), "test.rs", "This file has no TODOs");

        let result = regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", None).unwrap();
        assert!(
            result.contains("Found 0 results"),
            "Expected no results for files without matches."
        );
    }

    #[test]
    fn test_single_match() {
        let temp_dir = tempdir().unwrap();
        create_temp_file(
            temp_dir.path(),
            "test.rs",
            "This is a line.\nTODO: Fix this issue\nAnother line.",
        );

        let result = regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", None).unwrap();
        assert!(
            result.contains("TODO: Fix this issue"),
            "Expected to find a single TODO match."
        );
    }

    #[test]
    fn test_multiple_matches_with_context() {
        let temp_dir = tempdir().unwrap();
        create_temp_file(
            temp_dir.path(),
            "test.rs",
            "\
            Line 1\n\
            TODO: First match\n\
            Line 2\n\
            TODO: Second match\n\
            Line 3",
        );

        let result = regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", None).unwrap();
        assert!(
            result.contains("TODO: First match"),
            "Expected first match."
        );
        assert!(
            result.contains("TODO: Second match"),
            "Expected second match."
        );
    }

    #[test]
    fn test_file_pattern_filtering() {
        let temp_dir = tempdir().unwrap();
        create_temp_file(temp_dir.path(), "test.rs", "TODO: Match in RS file");
        create_temp_file(temp_dir.path(), "test.txt", "TODO: Match in TXT file");

        let result =
            regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", Some(".rs")).unwrap();

        assert!(
            result.contains("TODO: Match in RS file"),
            "Expected match in .rs file."
        );
        assert!(
            !result.contains("TODO: Match in TXT file"),
            "Did not expect match in .txt file."
        );
    }

    #[test]
    fn test_max_results_limit() {
        let temp_dir = tempdir().unwrap();
        let content = "TODO: Repeated match\n";

        // Create a file with more than MAX_RESULTS matches
        create_temp_file(temp_dir.path(), "test.rs", &content.repeat(400));

        let result = regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", None).unwrap();

        assert!(
            result.contains(&format!(
                "Showing first {} of {}+",
                MAX_RESULTS, MAX_RESULTS
            )),
            "Expected results to be limited to MAX_RESULTS."
        );
    }

    #[test]
    fn test_invalid_file_path() {
        let temp_dir = tempdir().unwrap();
        let invalid_path = temp_dir.path().join("nonexistent");

        let result = regex_search_files(temp_dir.path(), &invalid_path, "TODO:", None);
        assert!(
            result.is_ok(),
            "Expected the function to skip non-existent files."
        );
    }

    #[test]
    fn test_non_utf8_file_handling() {
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("non_utf8.bin");

        // Write invalid UTF-8 bytes to the file
        let mut file = File::create(&file_path).unwrap();
        file.write_all(&[0x80, 0x81, 0x82, 0xFF]).unwrap();

        let result = regex_search_files(temp_dir.path(), temp_dir.path(), "TODO:", None);
        assert!(
            result.is_err(),
            "Expected an error when reading non-UTF8 files."
        );
    }
}
