import json
from dataclasses import dataclass, field
from typing import Optional

from pypatronus import TransitionSystem, BitVec, ExprRef, BitVecVal


@dataclass
class FunctionalModel:
    name: str
    methods: list = field(default_factory=list)
    states: list = field(default_factory=list)


@dataclass
class Method:
    name: str
    inputs: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    state_updates: list = field(default_factory=list)
    # indicates whether the method can be executed based on state and inputs
    guard: Optional[ExprRef] = None


def verify_model(m: FunctionalModel):
    assert len(m.states) == 0, "TODO: deal with states"
    for method in m.methods:
        assert len(method.state_updates) == len(m.states)
        allowed_symbols = set(m.states) | set(method.inputs)

        for out_name, out_expr in method.outputs:
            unallowed = out_expr.symbols() - allowed_symbols
            assert len(unallowed) == 0, (
                f"Output {out_name}={out_expr} uses symbols that are neither inputs nor state: {unallowed}"
            )
        # check guard
        if method.guard is not None:
            unallowed = method.guard.symbols() - allowed_symbols
            assert len(unallowed) == 0, (
                f"Guard {method.guard} uses symbols that are neither inputs nor state: {unallowed}"
            )


def serialize(m: FunctionalModel, filename):
    assert len(m.states) == 0, "TODO: deal with states"
    verify_model(m)
    sys = TransitionSystem(name=m.name)
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

    info = {
        "name": m.name,
        "methods": [t.name for t in m.methods],
        "states": [s.name for s in m.states],
    }

    with open(filename, "w") as f:
        json.dump({"info": info, "sys": sys.to_btor2_str()}, f)
