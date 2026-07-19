#!/usr/bin/env python3
"""Generate the checked-in Runt configs from scripts/test_catalog.py.

Maybe we can do some more fancy validation on the catalog later,
not right now this script does no validation: paths are
assumed to be clean repo-relative posix strings and every config dir is
runt/<suite> (two levels below the repo root), which makes the relative path to
any test file simply "../../" + path.
"""

from __future__ import annotations

import json
import re
import shlex
import subprocess
from functools import lru_cache
from pathlib import Path
from collections import Counter

import test_catalog

REPO_ROOT = Path(__file__).resolve().parents[1]
RUNT_VERSION = "0.4.1"


def load_tx_cases() -> list[dict]:
    """Expand the compact catalog rows into the internal field shape.
    This handles default fields which are omitted in the catalog for
    the user experience."""
    out = []
    for path, c in test_catalog.TX_CASES.items():
        out.append(
            {
                "path": path,
                "protocol_path": c["protocol"],
                "module": c.get("top"),
                "verilog": c.get("verilog", ()),
                "max_steps": c.get("max_steps"),
                "extra_args": c.get("extra_args", ()),
                "expected": c["expect"],
            }
        )
    return out


def load_bi_cases() -> list[dict]:
    """Same idea as load_tx_cases but for the bi cases"""
    out = []
    for case_id, c in test_catalog.BI_CASES.items():
        out.append(
            {
                "id": case_id,
                "path": c["protocol"],
                "wave": c.get("wave"),
                "instances": c.get("instances", ()),
                "extra_args": c.get("extra_args", ()),
                "expected": c["expect"],
            }
        )
    return out


# helper function to escape globs in places
def runt_glob_literal(path: str) -> str:
    return path.replace("[", "[[]").replace("*", "[*]").replace("?", "[?]")


def replace_non_alphanumerics(value: object) -> str:
    text = re.sub(r"^-+", "", str(value).strip())
    return re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_") or "default"


def shared_bi_prot_files() -> frozenset[str]:
    # Set of `.prot` files which are used by more than one BI test case
    # (e.g. Antmicro and the Brave New World test cases for fixed/buggy wvaeforms
    # that share a single .prot file)

    counts = Counter(
        str(test_case["protocol"]) for test_case in test_catalog.BI_CASES.values()
    )
    return frozenset(file for (file, num_cases) in counts.items() if num_cases > 1)


def case_stem(case: dict) -> str:
    # Antmicro & Brave New World test cases for the BI share the same `.prot`
    # file but have multiple waveforms, so we use the waveform files'
    # names to identify a particular test, otherwise we use the `.prot` file's stem
    # to identify a test
    wave = case.get("wave")
    if wave and case["path"] in shared_bi_prot_files():
        return Path(wave).stem
    stem = Path(case["path"]).stem
    return stem.removesuffix(".bi")


def expect_name(case: dict, runner: str) -> str:
    # Each (test, runner) pair is unique, so stem + runner fully identifies the
    # expect file. The runner keeps interp/graph_interp goldens for the same .tx
    # from colliding.
    return f"{replace_non_alphanumerics(case_stem(case))}.{runner}.expect"


def expect_dir(case: dict, runner: str) -> str:
    wave = case.get("wave")
    base = Path(wave if runner == "bi" and wave else case["path"]).parent
    return f"../../{base.as_posix()}/expects"


# command construction


def binary_prefix(binary: str) -> list[str]:
    return [f"target/debug/{binary}"]


def repo_root_command(cmd: list[str], stderr: str = "discard") -> str:
    # Each runt test runs exactly one path, so we bake it straight into the
    # command. Runt captures stdout; interp snapshots intentionally include
    # diagnostics, while graph snapshots historically discard stderr.
    if stderr == "stdout":
        tail = " 2>&1"
    elif stderr == "discard":
        tail = " 2>/dev/null"
    elif stderr == "inherit":
        tail = ""
    else:
        raise ValueError(f"unknown stderr mode: {stderr}")
    return "cd ../.. && " + shlex.join(cmd) + tail


def timeout_cmd(timeout_secs: int, cmd: list[str]) -> list[str]:
    # Runt doesn't support expected timeouts, so we have to have this wrapper
    # on the interp/bi commands
    # Run in a new process group and kill the whole group (cargo's child binary
    # included) on expiry, exiting 124 to match coreutils.
    script = (
        "import os, signal, subprocess, sys\n"
        "p = subprocess.Popen(sys.argv[2:], start_new_session=True)\n"
        "try:\n"
        "    sys.exit(p.wait(timeout=float(sys.argv[1])))\n"
        "except subprocess.TimeoutExpired:\n"
        "    os.killpg(p.pid, signal.SIGKILL)\n"
        "    sys.exit(124)\n"
    )
    return ["python3", "-c", script, str(timeout_secs), *cmd]


def _tx_tail(cmd: list[str], case: dict, with_max_steps: bool) -> None:
    cmd += case["extra_args"]
    if case["verilog"]:
        cmd += ["--verilog", *case["verilog"]]
    if case["protocol_path"]:
        cmd += ["--protocol", case["protocol_path"]]
    if case["module"]:
        cmd += ["--module", case["module"]]
    if with_max_steps and case["max_steps"] is not None:
        cmd += ["--max-steps", str(case["max_steps"])]


# Each builder returns one or more (name_suffix, command) variants
# the suffix allows us to have differently named test cases with the same expect file


def interp_runt_command(case: dict) -> list[tuple[str, str]]:
    cmd = [
        *binary_prefix("protocols-interp"),
        "--color",
        "never",
        "--transactions",
        case["path"],
    ]
    _tx_tail(cmd, case, with_max_steps=True)
    return [("", repo_root_command(cmd, stderr="stdout"))]


def graph_interp_runt_command(case: dict) -> list[tuple[str, str]]:
    cmd = [*binary_prefix("graph-interp"), "--transactions", case["path"]]
    _tx_tail(cmd, case, with_max_steps=False)

    # wishbone and fifo only work with --respect-forks
    if case["path"].startswith("tests/fifo/") or case["path"].startswith(
        "tests/wishbone/"
    ):
        flag_sets = [("respect_forks", ["--respect-forks", "--determinize"])]
    else:
        # baseline and --contract-edges runs share one golden
        flag_sets = [
            ("", []),
            ("contract_edges", ["--contract-edges"]),
            ("respect_forks", ["--respect-forks", "--determinize"]),
        ]
    return [(suffix, repo_root_command(cmd + flags)) for suffix, flags in flag_sets]


def bi_runt_command(case: dict) -> list[tuple[str, str]]:
    # We pass in `--color never` to BI to suppress color in error messages
    # (so that the .expect files only display plaintext)
    cmd = [*binary_prefix("bi"), "--color", "never", "--protocol", case["path"]]
    if case["wave"]:
        cmd += ["--wave", case["wave"]]
    if case["instances"]:
        cmd += ["--instances", *case["instances"]]
    cmd += case["extra_args"]
    # We redirect stderr to stdout so that the expected output files
    # contain error messages if BI fails
    return [("", repo_root_command(cmd, stderr="stdout"))]


def waveform_runt_command(case: dict) -> list[tuple[str, str]]:
    ast_cmd = [
        *binary_prefix("protocols-interp"),
        "--color",
        "never",
        "--transactions",
        case["path"],
        "--ascii-waveform",
    ]
    _tx_tail(ast_cmd, case, with_max_steps=True)

    graph_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        case["path"],
        "--respect-forks",
        "--determinize",
        "--ascii-waveform",
    ]
    _tx_tail(graph_cmd, case, with_max_steps=False)

    ts_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        case["path"],
        "--transition-system",
        "--ascii-waveform",
    ]
    _tx_tail(ts_cmd, case, with_max_steps=False)

    return [
        ("ast", repo_root_command(ast_cmd, stderr="discard")),
        ("graph", repo_root_command(graph_cmd, stderr="discard")),
        ("ts", repo_root_command(ts_cmd, stderr="discard")),
    ]


def fail_runt_command(case: dict) -> list[tuple[str, str]]:
    graph_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        case["path"],
        "--respect-forks",
        "--determinize",
        "--brief-graph-errors",
    ]
    _tx_tail(graph_cmd, case, with_max_steps=False)

    ts_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        case["path"],
        "--transition-system",
    ]
    _tx_tail(ts_cmd, case, with_max_steps=False)

    return [
        ("graph", repo_root_command(graph_cmd, stderr="discard")),
        ("ts", repo_root_command(ts_cmd, stderr="discard")),
    ]


RUNT_BUILDERS = {
    "interp": interp_runt_command,
    "graph_interp": graph_interp_runt_command,
    "bi": bi_runt_command,
    "waveform": waveform_runt_command,
    "fail": fail_runt_command,
}


# config generation


@lru_cache(maxsize=None)
def protocol_constructs(protocol_path: str) -> frozenset[str]:
    """
    Constructs used anywhere in a .prot file, via `protocols-cli constructs`.
    """
    result = subprocess.run(
        [
            "cargo",
            "run",
            "-q",
            "--bin",
            "protocols-cli",
            "--",
            "-p",
            protocol_path,
            "constructs",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    used: set[str] = set()
    for line in result.stdout.splitlines():
        if ":" in line:
            _, constructs = line.split(":", 1)
            used.update(c.strip() for c in constructs.split(",") if c.strip())
    return frozenset(used)


# `.tx` files that are kept only for the AST interpreter
# and excluded from the graph interpreter for now
# (otherwise `.tx` files are shared between the AST & graph interpreters)
EXCLUDED_GRAPH_INTERPRETER_TEST_CASES = {
    "tests/fpga-debugging/axis-async-fifo-c4/c4_buggy.tx",
    "tests/fpga-debugging/axis-async-fifo-c4/c4_fixed.tx",
}


def graph_interp_cases(cases: list[dict]) -> list[dict]:
    """Passing tx cases whose protocol uses no for-in or repeat loop."""
    # Loop constructs the graph interpreter cannot handle (AST construct names).
    graph_interp_unsupported = {"for_in_loop", "repeat_loop"}

    selected = [
        c
        for c in cases
        if c["expected"] == "pass"
        and c["path"] not in EXCLUDED_GRAPH_INTERPRETER_TEST_CASES
        and not graph_interp_unsupported & protocol_constructs(c["protocol_path"])
    ]
    return sorted(selected, key=lambda c: c["path"])


def waveform_cases(cases: list[dict]) -> list[dict]:
    """All the graph_interp_cases, except with some extra exclusions"""
    # these cases are correct, but our ASCII diffing isn't good enough
    # for us to know they are the same
    xfailed = [
        # "examples/serv/serv_regfile.tx",
        "tests/adders/adder_d1/wait_and_add_correct.tx",
        "tests/identities/identity_d2/two_assignments_same_value.tx",
        # "tests/fifo/fifo.tx",
        # "tests/fifo/push_pop_identity_ok.tx",
        "tests/wishbone/wishbone.tx",
        "tests/brave_new_world/failure_to_update/ftu_sha_fix.tx",
    ]

    return list(filter(lambda c: c["path"] not in xfailed, graph_interp_cases(cases)))


def fail_cases(cases: list[dict]) -> list[dict]:
    """Runtime-failing tx cases whose graph and transition-system waveforms should match."""
    # Stuff like max steps and combinational dependency errors aren't enforced right now.
    runtime_failures = {"assertion_mismatch", "assignment_conflict"}
    graph_interp_unsupported = {"for_in_loop", "repeat_loop"}

    selected = [
        c
        for c in cases
        if c["expected"] in runtime_failures
        and c["path"] not in EXCLUDED_GRAPH_INTERPRETER_TEST_CASES
        and not graph_interp_unsupported & protocol_constructs(c["protocol_path"])
    ]
    return sorted(selected, key=lambda c: c["path"])


def runt_case_suites(suite_name: str, runner: str, cases: list[dict]):
    build = RUNT_BUILDERS[runner]
    suites = []
    for case in sorted(cases, key=lambda c: (c["path"], expect_name(c, runner))):
        path = case["path"]
        edir = expect_dir(case, runner)
        ename = expect_name(case, runner)
        base_name = (
            f"{suite_name}.{replace_non_alphanumerics(Path(path).with_suffix('').as_posix())}"
            f".{replace_non_alphanumerics(ename.removesuffix('.expect'))}"
        )
        for suffix, cmd in build(case):
            name = f"{base_name}.{suffix}" if suffix else base_name
            suites.append((name, edir, ename, cmd, path))
    return suites


def write_runt_toml(output_dir: Path, suites) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    chunks = [f"ver = {json.dumps(RUNT_VERSION)}\n"]
    for name, edir, ename, cmd, path in suites:
        chunks += [
            "[[tests]]",
            f"name = {json.dumps(name)}",
            "paths = [",
            f"  {json.dumps(runt_glob_literal('../../' + path))},",
            "]",
            f"expect_dir = {json.dumps(edir)}",
            f"expect_name = {json.dumps(ename)}",
            f"cmd = {json.dumps(cmd)}",
            "",
        ]
    (output_dir / "runt.toml").write_text("\n".join(chunks))


def generate_runt_configs() -> None:
    tx = load_tx_cases()
    bi = load_bi_cases()
    # Each suite maps a name to (runner, cases). interp + graph_interp
    # together cover every test.
    suite_specs = {
        "interp": ("interp", tx),
        "bi": ("bi", bi),
        "graph_interp": ("graph_interp", graph_interp_cases(tx)),
        "waveform": ("waveform", waveform_cases(tx)),
        "fail": ("fail", fail_cases(tx)),
    }

    # A golden may be shared by several variants of the same test (e.g. the
    # graph_interp baseline and --contract-edges runs), but two *different* tests
    # sharing one golden is an accidental name collision.
    expect_owner: dict[str, str] = {}
    for suite_name, (runner, cases) in suite_specs.items():
        config_dir = REPO_ROOT / "runt" / suite_name
        runt_suites = runt_case_suites(suite_name, runner, cases)
        for _name, edir, ename, _cmd, path in runt_suites:
            expect_path = (config_dir / edir / ename).resolve().as_posix()
            owner = expect_owner.setdefault(expect_path, path)
            if owner != path:
                raise SystemExit(
                    f"expectation name collision: {owner} and {path} -> {expect_path}"
                )
        write_runt_toml(config_dir, runt_suites)


def main() -> int:
    generate_runt_configs()
    print("wrote runt/*/runt.toml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
