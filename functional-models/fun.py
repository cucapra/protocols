import json
from dataclasses import dataclass, field
from pypatronus import TransitionSystem, BitVec


@dataclass
class FunctionalModel:
    name: str
    transactions: list = field(default_factory=list)
    states: list = field(default_factory=list)


@dataclass
class Transaction:
    name: str
    inputs: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    state_updates: list = field(default_factory=list)


def verify_model(m: FunctionalModel):
    assert len(m.states) == 0, "TODO: deal with states"
    for transaction in m.transactions:
        assert len(transaction.state_updates) == len(m.states)
        allowed_symbols = set(m.states) | set(transaction.inputs)

        for out_name, out_expr in transaction.outputs:
            unallowed = out_expr.symbols() - allowed_symbols
            assert len(unallowed) == 0, (
                f"Output {out_name} uses symbols that are neither inputs nor state: {unallowed}"
            )


def serialize(m: FunctionalModel, filename):
    assert len(m.states) == 0, "TODO: deal with states"
    verify_model(m)
    sys = TransitionSystem(name=m.name)
    for t in m.transactions:
        commit_signal = BitVec(f"{t.name}_commit", 1)
        sys.add_input(commit_signal)
        input_map = {}
        for inp in t.inputs:
            renamed = BitVec(f"{t.name}_in_{inp.name()}", inp.width())
            input_map[inp] = renamed
            sys.add_input(renamed)
        for out_name, out_expr in t.outputs:
            out_expr = out_expr.replace(input_map)
            sys.add_output(f"{t.name}_out_{out_name}", out_expr)

    transactions = [{"name": t.name} for t in m.transactions]
    info = {
        "name": m.name,
        "transactions": transactions,
        "states": [s.name for s in m.states],
        "sys": sys.to_btor2_str(),
    }

    with open(filename, "w") as f:
        json.dump(info, f)
