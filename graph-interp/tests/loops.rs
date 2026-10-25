use std::process::Command;

#[test]
fn loop_fixture_runs_after_standard_graph_passes() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_graph-interp"))
        .current_dir(root)
        .args([
            "--flow",
            "sequential",
            "--protocol",
            "tests/loops/loops.prot",
            "--verilog",
            "tests/loops/loops.v",
            "--transactions",
            "tests/loops/loops.tx",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("executed successfully"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}
