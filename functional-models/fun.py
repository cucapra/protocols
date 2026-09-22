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


def verify_model(m :FunctionalModel):
    for transaction in m.transactions:
        assert len(transaction.state_updates) == len(m.states)
        for output in transaction.outputs:
            # TODO: check symbols
            pass

def serialize(m :FunctionalModel):
    verify_model(m)

    inputs = []
    enables = []
    for t in m.transactions:
        inputs.append(BitVec(f"{t.name}_enable", 1))
        enables.append(inputs[-1])
        for inp in t.inputs:
            inputs.append(BitVec(f"{t.name}_in_{inp.name}", 1))

    sys = TransitionSystem(name=m.name)