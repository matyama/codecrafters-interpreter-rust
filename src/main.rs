use std::env;
use std::fs;

fn main() {
    let args = env::args().collect::<Vec<_>>();

    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
        return;
    }

    let command = &args[1];
    let filename = &args[2];

    match command.as_str() {
        "tokenize" => {
            let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
                eprintln!("Failed to read file {filename}");
                String::new()
            });

            if !file_contents.is_empty() {
                panic!("Scanner not implemented");
            } else {
                // Placeholder, remove this line when implementing the scanner
                println!("EOF  null");
            }
        }
        _ => {
            eprintln!("Unknown command: {command}");
        }
    }
}
