use rustc_hash::FxHashMap;

use crate::dut::PortId;
use crate::frontend::serialize::serialize_bitvec;
use crate::interpreter::Value;

fn format_wave_value(value: &Value, display_hex: bool) -> String {
    match value {
        Value::Concrete(bv) => serialize_bitvec(bv, display_hex),
        Value::DontCare => "x".to_string(),
    }
}

pub fn print_ascii_waveform(
    waveform: FxHashMap<PortId, Vec<Value>>,
    // because the interpreter and graph interpreter have different ways of
    // accessing the PatronusSim i.e. accessing the ports, we just get a lambda
    port_name: impl Fn(PortId) -> String,
    port_width: impl Fn(PortId) -> u32,
    display_hex: bool,
) {
    let mut rows: Vec<_> = waveform.into_iter().collect();
    rows.sort_by_key(|(port, _)| *port);

    let formatted_rows: Vec<_> = rows
        .into_iter()
        .map(|(port, values)| {
            let width = port_width(port);
            let label = if width == 1 {
                port_name(port)
            } else {
                format!("{}[{}:0]", port_name(port), width - 1)
            };
            let values: Vec<_> = values
                .iter()
                .map(|value| format_wave_value(value, display_hex))
                .collect();
            (label, values)
        })
        .collect();

    let label_width = formatted_rows
        .iter()
        .map(|(label, _)| label.len())
        .max()
        .unwrap_or(0);
    let value_width = formatted_rows
        .iter()
        .flat_map(|(_, values)| values.iter().map(|value| value.len()))
        .max()
        .unwrap_or(1);

    for (label, values) in formatted_rows {
        print!("{label:<label_width$}");
        for value in values {
            print!(" {value:>value_width$}");
        }
        println!();
    }
}
