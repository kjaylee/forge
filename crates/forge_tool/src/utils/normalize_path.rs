/// Normalize paths in snapshot content by replacing temporary directory
/// paths with [TEMP_DIR]
#[cfg(test)]
pub fn normalize_path(content: &str) -> String {
    let path_attribute = regex::Regex::new(r#"[a-zA-Z]*\.([a-z]*)""#).unwrap();
    let file_name = path_attribute
        .find(content)
        .unwrap()
        .as_str()
        .replace("\"", "");

    let new_path = format!("path=\"[TEMP_DIR]/{}\"", file_name);
    let pattern = regex::Regex::new(r#"path="[a-zA-Z0-9_/.]*""#).unwrap();
    let content = pattern.replace_all(content, &new_path);
    content.to_string()
}

#[test]
fn test_normalize_path() {
    let input = "<file_content path=\"/var/folders/xy/1234567890/T/.tmpABCDEF/test.txt\">Some test content</file_content>";
    let normalized = normalize_path(input);
    assert_eq!(
        normalized,
        "<file_content path=\"[TEMP_DIR]/test.txt\">Some test content</file_content>"
    );
}
