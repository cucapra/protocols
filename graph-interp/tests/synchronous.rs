use std::process::Command;

#[test]
fn driven_input_settles_before_same_cycle_output_branch() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    for flow in [
        "sequential",
        "trace-graph",
        "trace-system",
        "bounded-driver",
        "unbounded-driver",
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_graph-interp"));
        command.current_dir(root).args([
            "--transactions",
            "tests/synchronous/wire.tx",
            "--verilog",
            "tests/synchronous/wire.v",
            "--protocol",
            "tests/synchronous/wire.prot",
            "--flow",
            flow,
        ]);
        if flow == "bounded-driver" {
            command.args(["--bound", "2"]);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{flow}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("executed successfully"),
            "{flow}: {}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
}
