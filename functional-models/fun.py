import json
from dataclasses import dataclass, field
from typing import Optional, Tuple

from pypatronus import (
    TransitionSystem,
    State,
    BitVec,
    ExprRef,
    BitVecVal,
    If,
    Interpreter,
)


@dataclass
class Method:
    name: str
    inputs: list[ExprRef] = field(default_factory=list)
    outputs: list[Tuple[str, ExprRef]] = field(default_factory=list)
    nexts: Optional[list[ExprRef]] = None
    # indicates whether the method can be executed based on the current model state
    guard: Optional[ExprRef] = None


@dataclass
class FunctionalModel:
    name: str
    methods: list[Method] = field(default_factory=list)
    states: list[ExprRef] = field(default_factory=list)


class Sim:
    def __init__(self, model: FunctionalModel):
        self.sys = _build_sys(model)
        self.model = model
        self.sim = Interpreter(self.sys)
        for idx, m in enumerate(model.methods):
            # note: python lambdas capture the context instead of the value of idx be default which is why
            #       we need the nested lambdas!
            setattr(
                self,
                m.name,
                (
                    lambda ii: (
                        lambda *args, **kwargs: self._exec_method(ii, *args, **kwargs)
                    )
                )(idx),
            )

    def _exec_method(self, idx: int, *args, **kwargs):
        assert len(kwargs) == 0, "TODO: support keyword args"
        method = self.model.methods[idx]
        inputs = list(args)
        assert len(inputs) == len(method.inputs), (
            f"Wrong number of inputs {len(inputs)} != {len(method.inputs)}"
        )

        assert False, f"TODO: exec {method.name} {inputs}"


def verify_model(m: FunctionalModel):
    for method in m.methods:
        allowed_symbols = set(m.states) | set(method.inputs)

        for out_name, out_expr in method.outputs:
            unallowed = out_expr.symbols() - allowed_symbols
            assert len(unallowed) == 0, (
                f"Output {out_name}={out_expr} uses symbols that are neither inputs nor state: {unallowed}"
            )

        if method.nexts is not None:
            assert len(method.nexts) == len(m.states), (
                f"[{method.name}] {len(method.nexts)} next state assignments, but model has {len(m.states)} states."
            )
            for state, next in zip(m.states, method.nexts):
                assert state.sort() == next.sort(), (
                    f"[{method.name}] {state} : {state.sort()} = {next} : {next.sort()}"
                )
                unallowed = next.symbols() - allowed_symbols
                assert len(unallowed) == 0, (
                    f"[{method.name}] State update {state}={next} uses symbols that are neither inputs nor state: {unallowed}"
                )

        # check guard
        if method.guard is not None:
            allowed_symbols = set(m.states)
            unallowed = method.guard.symbols() - allowed_symbols
            assert len(unallowed) == 0, (
                f"Guard {method.guard} uses symbols that are not state: {unallowed}"
            )


def _build_sys(m: FunctionalModel) -> TransitionSystem:
    verify_model(m)
    sys = TransitionSystem(name=m.name)
    next_states = list(m.states)
    for t in m.methods:
        commit_signal = BitVec(f"{t.name}_commit", 1)
        sys.add_input(commit_signal)
        guard_signal = BitVecVal(1, 1) if t.guard is None else t.guard
        sys.add_output(f"{t.name}_guard", guard_signal)
        input_map = {}
        for inp in t.inputs:
            renamed = BitVec(f"{t.name}_in_{inp.name()}", inp.width())
            input_map[inp] = renamed
            sys.add_input(renamed)
        for out_name, out_expr in t.outputs:
            out_expr = out_expr.replace(input_map)
            sys.add_output(f"{t.name}_out_{out_name}", out_expr)
        if t.nexts is not None:
            for idx, next in enumerate(t.nexts):
                expr = next.replace(input_map)
                next_states[idx] = If(commit_signal, expr, next_states[idx])
    assert len(next_states) == len(m.states)
    sys.states = [
        State(sym.name(), next=next) for (sym, next) in zip(m.states, next_states)
    ]
    return sys


def serialize(m: FunctionalModel, filename):
    sys = _build_sys(m)

    info = {
        "name": m.name,
        "methods": [t.name for t in m.methods],
        "states": [s.name() for s in m.states],
    }

    print(sys)

    with open(filename, "w") as f:
        json.dump({"info": info, "sys": sys.to_btor2_str()}, f)
