# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
import pytest
from protocols import *


repo_root = (pathlib.Path(__file__) / ".." / ".." / "..").resolve()


def test_something():
    assert proto_test_fn() == 42
