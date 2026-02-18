# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>
from typing import Union, Optional

from .pyprotocols import *
from dataclasses import dataclass


@dataclass
class In:
    name: str
    width: int


@dataclass
class Out:
    name: str
    width: int


@dataclass
class DontCare:
    pass


X = DontCare()


def Prot(name: str, *args):
    p = Protocol(name, *args)
    return [p, *p.args]


def _is_arg(value) -> bool:
    return isinstance(value, In) or isinstance(value, Out)


def _is_value_type(value) -> bool:
    return _is_arg(value) or isinstance(value, DontCare)


def _get_width(value: Union[In, Out, DontCare]) -> Optional[int]:
    if isinstance(value, DontCare):
        return None
    else:
        return value.width


def _combine_widths(widths: list[Optional[int]]) -> Optional[int]:
    defined_widths = [w for w in widths if w is not None]
    if len(defined_widths) == 0:
        return None
    w = defined_widths[0]
    assert all(wi == w for wi in defined_widths), (
        f"Inconsistent widths: {defined_widths}"
    )
    return w


def _value_to_str(value: Union[In, Out, DontCare]) -> str:
    if isinstance(value, DontCare):
        return "X"
    else:
        return value.name


def _arg_to_str(arg: Union[In, Out]) -> str:
    if isinstance(arg, In):
        return f"in {arg.name}: u{arg.width}"
    else:
        return f"out {arg.name}: u{arg.width}"


class Protocol:
    def __init__(self, name: str, *args):
        self.name = name
        self.args: list[Union[In, Out]] = []
        for arg in args:
            assert isinstance(arg, In) or isinstance(arg, Out), (
                f"protocol arguments must be declared as `In` or `Out`, not `{type(arg)}`"
            )
            self.args.append(arg)
        self._finished = False
        self._lines = [
            f"prot {name}<dut: ???>({', '.join(_arg_to_str(a) for a in self.args)}) {{"
        ]
        self._indent = "  "
        # keeps track of all pins expected to be present in the dut
        self._dut_pins: dict[str, Optional[int]] = dict()

    def body(self) -> ProtocolBody:
        return ProtocolBody(self)

    def _stmt(self, stmt: str):
        self._lines.append(f"{self._indent}{stmt};")

    def step(self):
        assert not self._finished
        self._stmt("step()")

    def fork(self):
        assert not self._finished
        self._stmt("fork()")

    def finish(self):
        assert not self._finished
        self._lines.append("}")
        self._finished = True

    def _track_pin(self, pin_name: str, width: Optional[int]):
        if pin_name in self._dut_pins:
            self._dut_pins[pin_name] = _combine_widths(
                [self._dut_pins[pin_name], width]
            )
        else:
            self._dut_pins[pin_name] = width

    def assign_pin(self, pin_name: str, value: Union[In, Out, DontCare]):
        assert not self._finished
        assert _is_value_type(value)
        self._track_pin(pin_name, _get_width(value))
        self._stmt(f"dut.{pin_name} = {_value_to_str(value)}")

    def expect_pin(self, pin_name: str, value: Union[In, Out, DontCare]):
        assert not self._finished
        assert _is_value_type(value)
        self._track_pin(pin_name, _get_width(value))
        self._stmt(f"assert_eq(dut.{pin_name}, {_value_to_str(value)})")

    def __str__(self):
        assert self._finished
        return "\n".join(self._lines)


class ProtocolBody:
    def __init__(self, proto: Protocol):
        self.proto = proto

    def __enter__(self):
        return Dut(self.proto)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.proto.finish()


class Dut:
    def __init__(self, proto: Protocol):
        object.__setattr__(self, "proto", proto)

    def __setattr__(self, key, value: Union[In, Out, DontCare]):
        proto = object.__getattribute__(self, "proto")
        proto.assign_pin(key, value)

    def __getattr__(self, item: str) -> Pin:
        proto = object.__getattribute__(self, "proto")
        return Pin(proto, item)

    def __setitem__(self, key, value):
        proto = object.__getattribute__(self, "proto")
        proto.assign_pin(key, value)

    def __getitem__(self, item):
        proto = object.__getattribute__(self, "proto")
        return Pin(proto, item)


class Pin:
    def __init__(self, proto: Protocol, name: str):
        self.proto = proto
        self.name = name

    def expect(self, value: Union[In, Out, DontCare]):
        self.proto.expect_pin(self.name, value)
