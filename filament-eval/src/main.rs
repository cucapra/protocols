// Copyright 2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use anyhow::anyhow;
use clap::Parser;
use protocols::ir::Dir;
use protocols::ir::Struct;
use protocols::serialize::serialize_struct;
use serde_json::Value;
use std::io::stdout;
use std::{cmp::max, path::Path};

use types::RawParameter;

use types::Events;

use crate::types::Event;

mod types;

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

/// Produces a Protocols struct definition based on the Filament interface
fn generate_struct(json: &Value, name: String) -> Struct {
    let inputs = json["inputs"]
        .as_array()
        .expect("Expected `inputs` to be a JSON array");
    let mut struct_fields = vec![];
    for input in inputs {
        let raw_param: RawParameter = serde_json::from_value(input.clone())
            .expect("Unable to convert JSON object into input `RawParameter`");
        let input_field = raw_param.into_field(Dir::In);
        struct_fields.push(input_field);
    }
    let outputs = json["outputs"]
        .as_array()
        .expect("Expected `outputs` to be a JSON array");
    for output in outputs {
        let raw_param: RawParameter = serde_json::from_value(output.clone())
            .expect("Unable to convert JSON object into output `RawParameter");
        let output_field = raw_param.into_field(Dir::Out);
        struct_fields.push(output_field);
    }
    Struct {
        name,
        pins: struct_fields,
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

        // Treat the file-stem of the JSON filepath as the name of the
        // Protocols struct (this involves converting from `OsStr` to `String`)
        let dut_name: String = filepath.file_stem().map_or_else(
            || panic!("Unable to extract file stem from filepath"),
            |os_str| {
                os_str
                    .to_str()
                    .expect("Unable to convert `OsStr` to `&str`")
                    .to_uppercase()
            },
        );
        let protocols_struct = generate_struct(&json, dut_name);

        serialize_struct(&mut stdout(), &protocols_struct)?;
        Ok(())
    } else {
        Err(anyhow!(
            "Invalid extension for file {filepath_str}, expected JSON file"
        ))
    }
}
