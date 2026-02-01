use std::{env, path::Path};

use serde_json::Value;

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.is_empty() {
        panic!("Missing argument")
    } else if args.len() >= 2 {
        panic!("Too many arguments supplied")
    }
    let filepath_str = &args[0];
    let filepath = Path::new(filepath_str);

    if let Some("json") = filepath.extension().and_then(|s| s.to_str()) {
        let file_contents = std::fs::read_to_string(filepath)?;
        let _json: Value = serde_json::from_str(&file_contents)
            .unwrap_or_else(|_| panic!("Unable to read from JSON file {filepath_str}"));
        Ok(())
    } else {
        panic!("Invalid extension for file {filepath_str}, expected JSON file");
    }
}
