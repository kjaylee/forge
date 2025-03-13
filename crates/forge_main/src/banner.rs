use std::io;

use colored::Colorize;

use crate::model::ForgeCommandManager;

const BANNER: &str = include_str!("banner");

pub fn display(command_manager: &ForgeCommandManager) -> io::Result<()> {
    let commands = command_manager
        .list()
        .into_iter()
        .map(|command| command.name)
        .collect::<Vec<_>>();
    // Split the banner into lines and display each line dimmed
    println!("{} {}", BANNER.dimmed(), commands.join(", ").bold());
    Ok(())
}
