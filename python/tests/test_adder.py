# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
from protocols import *


ADD_PROT = """
prot add<dut: ???>(in a: u32, in b: u32, out s: u32) {
  dut.a = a;
  dut.b = b;
  step();
  dut.a = X;
  dut.b = X;
  assert_eq(dut.s, s);
  fork();
  step();
}
"""


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

    assert str(p).strip() == ADD_PROT.strip()
