use std::{collections::HashSet, path::PathBuf};


/// Close small gaps between shown lines and handle blank lines appropriately
pub fn close_small_gaps_helper(
    lines: HashSet<usize>,
    code_split_by_lines: Vec<String>,
    code_len: usize,
) -> HashSet<usize> {
    let mut closed_show = lines.clone();
    let mut sorted_show: Vec<usize> = lines.iter().cloned().collect();
    sorted_show.sort_unstable();

    // Close gaps of size 1 (where i and i+2 are present but i+1 is missing)
    for (i, &value) in sorted_show.iter().enumerate().take(sorted_show.len() - 1) {
        if sorted_show[i + 1] - value == 2 {
            closed_show.insert(value + 1);
        }
    }

    // Pick up adjacent blank lines if they appear after non-empty lines
    for (i, line) in code_split_by_lines.iter().enumerate() {
        if !closed_show.contains(&i) {
            continue;
        }

        if !line.trim().is_empty() 
            && i < code_len - 2
            && code_split_by_lines[i + 1].trim().is_empty() 
        {
            closed_show.insert(i + 1);
        }
    }

    closed_show
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_close_small_gaps() {
        let code = r#"fn test() {
    let x = 1;

    let y = 2;
    
    println!("{}", x + y);
}"#;
        let mut lines = HashSet::new();
        lines.insert(0);  // fn test() {
        lines.insert(2);  // blank line
        lines.insert(4);  // blank line
        
        let code_lines: Vec<String> = code.lines().map(|l| l.to_string()).collect();
        let code_len = code_lines.len();
        
        let closed = close_small_gaps_helper(lines, code_lines, code_len);
        
        // Should include line 1 since it's between 0 and 2
        assert!(closed.contains(&1), "Should close gap between lines 0 and 2");
        // Should include line 3 since it's between 2 and 4
        assert!(closed.contains(&3), "Should close gap between lines 2 and 4");
    }

    #[test]
    fn test_blank_line_handling() {
        let code = r#"fn test() {
    let x = 1;

    let y = 2;
    println!("{}", x + y);
}"#;
        let mut lines = HashSet::new();
        lines.insert(1);  // let x = 1;
        
        let code_lines: Vec<String> = code.lines().map(|l| l.to_string()).collect();
        let code_len = code_lines.len();
        
        let closed = close_small_gaps_helper(lines, code_lines, code_len);
        
        // Should include the blank line after let x = 1
        assert!(closed.contains(&2), "Should include blank line after non-empty line");
    }
}