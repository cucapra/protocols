use baa::{BitVecOps, Value};
use patronus::expr::Context;
use patronus::sim::{InitKind, Interpreter, Simulator};
use protocols::backends::monitor_transition_system::into_monitor_transition_system;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::ir::joint_monitor::build_joint_monitor_automaton;
use protocols::waveform::{CallbackResult, Instance, SignalTrace, WaveformTrace, sampling_mode};

use super::Cli;

pub fn run(cli: &Cli) -> Result<bool, String> {
    let mut diagnostics = DiagnosticHandler::new(clap::ColorChoice::Never, false, false, false);
    let (mut symbols, modules) = protocols::frontend(
        &cli.protocol,
        &mut diagnostics,
        cli.skip_static_step_fork_checks,
        false,
    )
    .map_err(|e| e.to_string())?;
    let instances = cli
        .instances
        .iter()
        .map(|arg| Instance::parse(&modules, arg))
        .collect::<Result<Vec<_>, _>>()?;
    let sampling = sampling_mode(&modules, &instances, cli.sample_posedge.clone())?;
    let mut trace = WaveformTrace::open(
        cli.wave.as_ref().unwrap(),
        &symbols,
        &modules,
        &instances,
        sampling,
        cli.force_x_to_zero,
    )?;
    // Each waveform instance has its own state and bank heads. They consume the
    // same sample stream, and the combined interpretation requires all to survive.
    let systems = instances
        .iter()
        .map(|instance| {
            let module = &modules[instance.module_id];
            let mut ctx = Context::default();
            let monitor =
                build_joint_monitor_automaton(&mut ctx, module.protos.clone(), &mut symbols)
                    .map_err(|e| e.to_string())?;
            let lowered = into_monitor_transition_system(&mut ctx, &monitor, module, &symbols);
            Ok((ctx, lowered))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut simulators = systems
        .iter()
        .map(|(ctx, lowered)| {
            let mut sim = Interpreter::new(ctx, &lowered.ts);
            sim.init(InitKind::Zero);
            sim
        })
        .collect::<Vec<_>>();
    let mut failed = false;
    let mut error = None;
    trace.stream_steps(|step, values| {
        for (instance_id, ((_, lowered), simulator)) in systems.iter().zip(&mut simulators).enumerate() {
            for (&pin, &input) in &lowered.pin_inputs {
                simulator.set(input, values.get(instance_id as u32, pin));
            }
            simulator.step();
            if matches!(simulator.get(lowered.internal_error), Value::BitVec(value) if value.is_true()) {
                error = Some(format!("internal monitor error at sample {step}, instance {}", instances[instance_id].name));
                return CallbackResult::Stop;
            }
            if matches!(simulator.get(lowered.bad), Value::BitVec(value) if value.is_true()) {
                failed = true;
            }
        }
        if failed { CallbackResult::Stop } else { CallbackResult::Continue }
    })?;
    if let Some(error) = error {
        Err(error)
    } else {
        Ok(failed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::Parser;

    const PROTOCOL: &str = r#"
        struct Dut { in a: u2, out b: u2, }
        prot check<DUT: Dut>(p: u2) {
            DUT.a := p; step();
            DUT.a := X; assert_eq(p, DUT.b); step();
        }
    "#;

    fn check(wave: &str, instances: &[&str]) -> Result<bool, String> {
        let directory = tempfile::tempdir().unwrap();
        let protocol = directory.path().join("test.prot");
        let waveform = directory.path().join("test.wave");
        std::fs::write(&protocol, PROTOCOL).unwrap();
        std::fs::write(&waveform, wave).unwrap();
        let mut args = vec![
            "graph-interp".to_string(),
            "--flow".to_string(),
            "unbounded-monitor".to_string(),
            "--protocol".to_string(),
            protocol.display().to_string(),
            "--wave".to_string(),
            waveform.display().to_string(),
            "--instances".to_string(),
        ];
        args.extend(instances.iter().map(|s| s.to_string()));
        let cli = Cli::try_parse_from(args).unwrap();
        crate::validate_cli(&cli).unwrap();
        run(&cli)
    }

    #[test]
    fn empty_and_unfinished_prefixes_pass_without_an_extra_sample() {
        assert_eq!(check("a[1:0]\nb[1:0]\n", &[":Dut"]), Ok(false));
        assert_eq!(check("a[1:0] 1\nb[1:0] 0\n", &[":Dut"]), Ok(false));
    }

    #[test]
    fn last_sample_determines_failure() {
        assert_eq!(check("a[1:0] 1 0\nb[1:0] 0 1\n", &[":Dut"]), Ok(false));
        assert_eq!(check("a[1:0] 1 0\nb[1:0] 0 2\n", &[":Dut"]), Ok(true));
    }

    #[test]
    fn every_waveform_instance_must_survive() {
        let good = "left.a[1:0] 1 0\nleft.b[1:0] 0 1\nright.a[1:0] 3 0\nright.b[1:0] 0 3\n";
        assert_eq!(check(good, &["left:Dut", "right:Dut"]), Ok(false));
        assert_eq!(
            check(
                &good.replace("right.b[1:0] 0 3", "right.b[1:0] 0 2"),
                &["left:Dut", "right:Dut"]
            ),
            Ok(true)
        );
    }

    #[test]
    fn an_invalid_instance_is_an_error_rather_than_a_trace_failure() {
        assert!(check("a[1:0] 0\nb[1:0] 0\n", &[":Unknown"]).is_err());
    }
}
