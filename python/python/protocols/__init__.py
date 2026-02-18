# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>
from typing import Union

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


class Protocol:
    def __init__(self, name: str, *args):
        self.name = name
        self.args: list[Union[In, Out]] = []
        for arg in args:
            assert isinstance(arg, In) or isinstance(arg, Out), (
                f"protocol arguments must be declared as `In` or `Out`, not `{type(arg)}`"
            )
            self.args.append(arg)

    def body(self) -> ProtocolBody:
        return ProtocolBody(self)

    def step(self):
        print("STEP")


class ProtocolBody:
    def __init__(self, proto: Protocol):
        self.proto = proto

    def __enter__(self):
        return Dut(self)

    def __exit__(self, exc_type, exc_val, exc_tb):
        print("BODY exit")


class Dut:
    def __init__(self, body: ProtocolBody):
        self.body = body

    def __setattr__(self, key, value):
        print(f"TODO: {key} = {value}")

    def __getattr__(self, item):
        print(f"TODO: get {item}")
        return None
