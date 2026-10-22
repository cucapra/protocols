use patronus::expr::Context;
use rustc_hash::FxHashSet;

use crate::frontend::symbol::SymbolTable;
use crate::ir::driver_to_monitor::MonitorAutomaton;
use crate::ir::register_simplify::simplify_registers;

/// Simplify ordinary register state; monitor ownership remains in this adapter.
pub fn simplify_monitor(
    ctx: &mut Context,
    mut monitor: MonitorAutomaton,
    symbols: &mut SymbolTable,
) -> MonitorAutomaton {
    // Joint construction adds liveness reads after this simplification.
    let preserved = FxHashSet::from_iter([monitor.live_register]);
    let entry = monitor.graph.entry;
    let dead = simplify_registers(
        ctx,
        &mut monitor.graph,
        symbols,
        entry,
        &monitor.register_inits,
        &preserved,
    );
    monitor.register_inits.retain(|r, _| !dead.contains(r));
    monitor.value_registers.retain(|_, r| !dead.contains(r));
    monitor.knownness_registers.retain(|_, r| !dead.contains(r));
    monitor.graph.garbage_collect_unreachable(ctx, false);
    monitor
}
