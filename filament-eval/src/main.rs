use clap::Parser;
use serde::Deserialize;
use serde_json::Value;
use std::{fmt, path::Path};

/// CLI arguments for the Filament to Protocols compiler
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

/// A Filament event variable
#[derive(Debug, Deserialize, Clone, PartialEq)]
struct Event {
    /// The name of the event
    name: String,

    /// The delay associated with the event
    delay: u32,
}

impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}: {}>", self.name, self.delay)
    }
}

/// Extracts all the `Event`s from the Filament interface JSON
fn get_events(json: &Value) -> Vec<Event> {
    let interface_ports = json["interfaces"]
        .as_array()
        .expect("Expected `interfaces` to be a JSON array");
    let mut events = vec![];
    for port in interface_ports {
        let event_name = port["event"]
            .as_str()
            .expect("Expected `event` to be a string")
            .to_string();
        let delay = port["delay"]
            .as_i64()
            .expect("Expected `delay` to be an integer") as u32;
        let event = Event {
            name: event_name,
            delay,
        };
        events.push(event);
    }
    events
}

/// Main entry point for the executable
fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let filepath_str = cli.json;
    let filepath = Path::new(&filepath_str);

    if let Some("json") = filepath.extension().and_then(|s| s.to_str()) {
        let file_contents = std::fs::read_to_string(filepath)?;
        let json: Value = serde_json::from_str(&file_contents)
            .unwrap_or_else(|_| panic!("Unable to read from JSON file {filepath_str}"));
        let events = get_events(&json);
        println!("events: {:?}", events);
        Ok(())
    } else {
        panic!("Invalid extension for file {filepath_str}, expected JSON file");
    }
}
