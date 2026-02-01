use clap::Parser;
use serde_json::Value;
use std::path::Path;

#[derive(Parser)]
#[command(
    version,
    about = "Compiles Filament types to Protocols",
    disable_version_flag = true
)]
struct Cli {
    /// Path to a JSON file for a Filament interface
    #[arg(short, long, value_name = "FILAMENT_INTERFACE_JSON_FILE")]
    json: String,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let filepath_str = cli.json;
    let filepath = Path::new(&filepath_str);

    if let Some("json") = filepath.extension().and_then(|s| s.to_str()) {
        let file_contents = std::fs::read_to_string(filepath)?;
        let _json: Value = serde_json::from_str(&file_contents)
            .unwrap_or_else(|_| panic!("Unable to read from JSON file {filepath_str}"));
        Ok(())
    } else {
        panic!("Invalid extension for file {filepath_str}, expected JSON file");
    }
}
