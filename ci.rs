use std::process::Command;

fn main() {
    let output = Command::new("cargo")
        .arg("test")
        .output()
        .expect("Failed to execute command");

    if !output.status.success() {
        println!("Tests failed");
        std::process::exit(1);
    }

    println!("Tests passed");
}
