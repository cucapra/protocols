use baa::{BitVecOps, Value};
use bi::Instance;
use bi::signal_trace::{
    AsciWaveTrace, CallbackResult, SignalTrace, WaveSamplingMode, WaveSignalTrace,
};
use patronus::expr::Context;
use patronus::sim::{InitKind, Interpreter, Simulator};
use protocols::backends::monitor_transition_system::into_monitor_transition_system;
use protocols::frontend::Module;
use protocols::frontend::ast::Clock;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::ir::joint_monitor::build_joint_monitor_automaton;

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
        .map(|arg| parse_instance(&modules, arg))
        .collect::<Result<Vec<_>, _>>()?;
    let sampling = sampling_mode(&modules, &instances, cli.sample_posedge.clone())?;
    // Each waveform instance has its own state and bank heads. They consume the
    // same sample stream, and our simple pass/fail interpretation requires all to survive.
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
    let mut check_sample = |step, values: bi::signal_trace::SignalValues<'_>| {
        for (instance_id, ((_, lowered), simulator)) in
            systems.iter().zip(&mut simulators).enumerate()
        {
            for (&pin, &input) in &lowered.pin_inputs {
                simulator.set(input, values.get(instance_id as u32, pin));
            }
            simulator.step();
            if matches!(simulator.get(lowered.internal_error), Value::BitVec(value) if value.is_true())
            {
                error = Some(format!(
                    "internal monitor error at sample {step}, instance {}",
                    instances[instance_id].name
                ));
                return CallbackResult::Stop;
            }
            if matches!(simulator.get(lowered.bad), Value::BitVec(value) if value.is_true()) {
                failed = true;
            }
        }
        if failed {
            CallbackResult::Stop
        } else {
            CallbackResult::Continue
        }
    };
    if let Ok(mut trace) = WaveSignalTrace::open(
        cli.wave.as_ref().unwrap(),
        &symbols,
        &modules,
        &instances,
        sampling,
        cli.force_x_to_zero,
    ) {
        trace.stream_steps(&mut check_sample)?;
    } else {
        let mut trace = AsciWaveTrace::open(
            cli.wave.as_ref().unwrap(),
            &modules,
            &instances,
            cli.force_x_to_zero,
        )
        .map_err(|e| e.to_string())?;
        trace.stream_steps(&mut check_sample)?;
    }
    if let Some(error) = error {
        Err(error)
    } else {
        Ok(failed)
    }
}

fn parse_instance(modules: &[Module], arg: &str) -> Result<Instance, String> {
    let (name, module) = arg
        .split_once(':')
        .ok_or_else(|| format!("unexpected instance argument: {arg}"))?;
    let module_id = modules
        .iter()
        .position(|m| m.name == module)
        .ok_or_else(|| format!("Unknown design {module} for instance {name}"))?;
    Ok(Instance {
        name: name.to_string(),
        module: module.to_string(),
        module_id,
    })
}

fn sampling_mode(
    modules: &[Module],
    instances: &[Instance],
    posedge: Option<String>,
) -> Result<WaveSamplingMode, String> {
    let mut clocks = instances
        .iter()
        .filter_map(|instance| {
            let full_name = |name: &str| {
                if instance.name.is_empty() {
                    name.to_string()
                } else {
                    format!("{}.{name}", instance.name)
                }
            };
            match &modules[instance.module_id].clock {
                Clock::None => None,
                Clock::PosEdge(name) => Some(Clock::PosEdge(full_name(name))),
                Clock::NegEdge(name) => Some(Clock::NegEdge(full_name(name))),
            }
        })
        .collect::<Vec<_>>();
    if let Some(name) = posedge {
        clocks.push(Clock::PosEdge(name));
    }
    clocks.sort();
    clocks.dedup();
    match clocks.as_slice() {
        [] => Ok(WaveSamplingMode::Direct),
        [Clock::PosEdge(name)] => Ok(WaveSamplingMode::RisingEdge(name.clone())),
        [Clock::NegEdge(name)] => Ok(WaveSamplingMode::FallingEdge(name.clone())),
        other => Err(format!("Too many clocks: {other:?}")),
    }
}
