# Meta-Automaton Lowering

## Definitions

- **Concrete control node:** A node in a contracted protocol graph. It is the
  exact control-flow location at which that protocol is paused, including the
  actions and guarded step transitions available there. In particular, it is
  not a timing-meta node and it is not a loop iteration counter.
- **Meta node:** A node in the timing meta-automaton. It records scheduling
  information such as live transactions, post-phase positions, banking, and
  rotations, but may intentionally omit the exact control node inside an
  unbounded pre-phase loop.
- **Lowered driver state:** A node in the final regular driver graph. For a
  pre-phase protocol, it represents the product of a meta node and a concrete
  control node:

  ```text
  (meta node, concrete control node)
  ```

  Choice and completed meta nodes do not have a pre-phase control node, so
  they use a single lowered state per meta node.

## Goal

Lower a timing meta-automaton into a regular protocol graph while preserving
the concrete control-flow location of every protocol in its pre-phase.

The timing meta-automaton records information such as:

- which transactions are live;
- which protocol is currently being selected or executed;
- post-phase cycle positions;
- bank rotations.

It does not record the concrete control-flow node of an unbounded pre-phase.
The lowering adds that missing information.

## Lowered State

For every meta node with a pre-phase frontier, create one regular graph node for
each reachable concrete pre-phase control node.

Conceptually, each lowered state is:

```text
(meta node, concrete frontier control node)
```

Choice and completed states use one regular node because they have no concrete
pre-phase frontier.

Live post-phase transactions are taken from the meta node. Their actions and
cycle positions are copied into every concrete frontier variant.

## Construction

1. Lower every protocol into a contracted `ProtoGraph`.
2. Find the reachable control nodes before `Fork` or `Done`.
3. For every meta `Pre` node, allocate one regular node per reachable control
   node.
4. Copy actions from all live post-phase transactions into every variant.
5. Copy actions from the variant's concrete frontier control node.
6. For a `Choice` node, add the entry actions for every selectable protocol,
   guarded by `node_choice`.
7. Add transitions by inspecting the concrete step transitions from each
   frontier control node.

The same concrete control node may be revisited indefinitely by a loop, but it
is allocated only once. This is why an unbounded loop does not cause infinite
unrolling.

## Boundary Handling

For an unbounded pre-phase, a concrete transition is classified using the
protocol graph:

- A `Fork` action marks a fork boundary.
- A transition into `Done` marks a completion boundary.
- Anything else is a pre-phase continuation.

The meta fork/finish edge is enabled only when the concrete boundary guard is
true.

For example:

```text
w_loop_guard --!ready--> w_loop_body
w_loop_guard -- ready--> w_after_wait
w_after_wait             --> w_assign_b
w_assign_b               --> w_assert
w_assert                 --> Done
```

The lowered graph contains the corresponding finite states:

```text
choice -> w_loop_guard
w_loop_guard --!ready--> w_loop_body
w_loop_body             --> w_loop_guard
w_loop_guard --ready--> w_after_wait
w_after_wait             --> w_assign_b
w_assign_b               --> w_assert
w_assert                 --> choice
```

The `choice` transition cannot complete `w` directly, because the concrete
graph does not reach `Done` there.

## Live Transactions

For each live transaction in a meta state:

1. Select its post-phase control node from the meta post-cycle position.
2. Copy its actions into the lowered state.
3. Conjoin its step guard with the frontier guard.
4. Preserve the rotation annotations on the resulting transition.

The transition guard therefore represents the condition under which all active
protocol units can advance synchronously.

## Banking and Rotations

Instance substitutions use the meta instance number to select the logical bank
for protocol arguments.

Meta transitions retain their existing bank rotation annotations. A rotation is
applied when the corresponding steady-state backedge is taken, changing the
mapping between logical instance numbers and physical banks without changing
the concrete control state.

## Determinism

The lowered graph retains guarded alternatives from the protocol graph. The
existing subset construction can then convert it to a DFA:

```text
lowered graph -> determinized(lowered graph)
```

The regression tests run determinization on the unbounded example and on a
straight-line add/sub driver. They also check explicit graph-size bounds.

## Termination

The construction reaches a fixed point because it explores a finite product of:

```text
meta nodes
× concrete pre-phase control nodes
× finite live post-phase configurations
```

Loop iterations reuse existing `(meta node, control node)` variants. No state
stores an unbounded elapsed-cycle counter.

## Current Scope

The implementation currently assumes:

- post-phases are linear and have statically known lengths;
- protocol banking and rotations come from the existing meta-automaton;
- internal assertion behavior is not expanded by this lowering.

The main extension point is replacing the linear post-phase lookup with the
same concrete-control-state expansion used for pre-phases.
