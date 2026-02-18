# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
from protocols import *


def test_adder_protocol():
    p, a, b, s = Prot("add", In("a", 32), In("b", 32), Out("s", 32))
    with p.body() as dut:
        dut.a = a
        dut.b = b
        p.step()
        dut.a = X
        dut.b = X
        dut.s.expect(s)
        p.fork()
        p.step()
    assert str(p) == "TODO"
