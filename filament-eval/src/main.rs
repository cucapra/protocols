use clap::Parser;
use serde::Deserialize;
use serde_json::Value;
use std::{cmp::max, fmt, path::Path};

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

/// Tuple struct so that we can implement `Display` for `Vec<Event>`
/// Rust doesn't allow us to do `impl Display for Vec<Event>` directly due to
/// the orphan rule (neither `Display` nor `Vec` are defined in this crate).
struct Events(Vec<Event>);

impl fmt::Display for Events {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let event_strs: Vec<String> = self.0.iter().map(|e| e.to_string()).collect();
        write!(f, "[{}]", event_strs.join(", "))
    }
}

/// Extracts all the `Event`s from the Filament interface JSON contained
/// in the `json` argument
fn get_events(json: &Value) -> Events {
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
    Events(events)
}

/// Computes the max time interval out of all the output ports in the Filament type
/// The argument `json` is the JSON representing the Filament signature.
fn find_max_time(json: &Value) -> u32 {
    let outputs = json["outputs"]
        .as_array()
        .expect("Expected `outputs` to be a JSON array");
    let mut max_end_time = 0;
    for output in outputs {
        let end_time = output["end"].as_i64().expect("Expected `end` to be an int") as u32;
        max_end_time = max(max_end_time, end_time);
    }
    max_end_time
}

/// Main entry point for the executable
/// Example: cargo run -- --json tests/add.json
/// TODO: add Turnt tests
fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let filepath_str = cli.json;
    let filepath = Path::new(&filepath_str);

    if let Some("json") = filepath.extension().and_then(|s| s.to_str()) {
        let file_contents = std::fs::read_to_string(filepath)?;
        let json: Value = serde_json::from_str(&file_contents)
            .unwrap_or_else(|_| panic!("Unable to read from JSON file {filepath_str}"));
        let events = get_events(&json);
        let max_time = find_max_time(&json);
        println!("events: {}, max_time = {}", events, max_time);
        Ok(())
    } else {
        panic!("Invalid extension for file {filepath_str}, expected JSON file");
    }
}
