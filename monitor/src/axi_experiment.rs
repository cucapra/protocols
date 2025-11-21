#[cfg(test)]
mod tests {
    use crate::designs::{Design, Instance};
    use crate::signal_trace::{SignalTrace, StepResult, WaveSignalTrace};
    use baa::BitVecOps;
    use protocols::ir::{Dir, Field, SymbolTable, Type};
    use rustc_hash::FxHashMap;

    // cargo test test_axi_rising_edge_sampling -- --nocapture
    #[test]
    fn test_axi_rising_edge_sampling() {
        // Set up the symbol table and symbol IDs
        let mut symbol_table = SymbolTable::default();

        // Add symbols to the symbol table and get their IDs
        let valid_id =
            symbol_table.add_without_parent("m_axis_tvalid".to_string(), Type::BitVec(1));
        let ready_id =
            symbol_table.add_without_parent("m_axis_tready".to_string(), Type::BitVec(1));
        let data_id = symbol_table.add_without_parent("m_axis_tdata".to_string(), Type::BitVec(8));

        // Create a dummy SymbolId for the design itself
        let design_id = symbol_table.add_without_parent("AXIS".to_string(), Type::Unknown);

        // Create the Design for AXIS
        let axis_design = Design {
            name: "AXIS".to_string(),
            symbol_id: design_id,
            pins: vec![
                (
                    ready_id,
                    Field::new("m_axis_tready".to_string(), Dir::Out, Type::BitVec(1)),
                ),
                (
                    valid_id,
                    Field::new("m_axis_tvalid".to_string(), Dir::In, Type::BitVec(1)),
                ),
                (
                    data_id,
                    Field::new("m_axis_tdata".to_string(), Dir::In, Type::BitVec(8)),
                ),
            ],
            transaction_ids: vec![],
        };

        let mut designs = FxHashMap::default();
        designs.insert("AXIS".to_string(), axis_design);

        // Create the instance
        let instances = vec![Instance {
            name: "uut_rx".to_string(),
            design_name: "AXIS".to_string(),
        }];

        // Load the waveform with rising edge sampling on uut_rx.clk
        let mut trace = WaveSignalTrace::open(
            &"tests/wal/advanced/uart-axi.fst",
            &designs,
            &instances,
            Some("uut_rx.clk".to_string()),
        )
        .expect("Failed to load waveform");

        // Instance ID is 0 since we only have one instance
        let instance_id = 0;

        // Track the waveform times where both valid and ready are 1, along with the data value
        let mut waveform_times = Vec::new();
        let mut data_values = Vec::new();

        loop {
            // Get the current values of valid, ready, and data
            let valid_val = trace
                .get(instance_id, valid_id)
                .expect("Failed to get valid signal");
            let ready_val = trace
                .get(instance_id, ready_id)
                .expect("Failed to get ready signal");
            let data_val = trace
                .get(instance_id, data_id)
                .expect("Failed to get data signal");

            // Check if both ready and valid are 1
            if valid_val.to_u64() == Some(1) && ready_val.to_u64() == Some(1) {
                waveform_times.push(trace.time_value(trace.time_step()));
                data_values.push(data_val.to_u64().unwrap_or(0));
            }

            // Advance to the next rising edge
            match trace.step() {
                StepResult::Ok => (),
                StepResult::Done => break,
            }
        }

        println!("Data values: {:?}", data_values);

        println!("\nTime for each data value:");
        for (&time_fs, &data_val) in waveform_times.iter().zip(data_values.iter()) {
            // Convert fs to ns for readability
            let time_ns = time_fs / 1_000_000;
            println!(" time: {}ns, data = {}", time_ns, data_val);
        }

        assert_eq!(data_values, vec![0, 1, 2, 3, 8, 9, 10, 11, 12, 15, 18, 19]);
    }
}
