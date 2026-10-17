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

import test_catalog

REPO_ROOT = Path(__file__).resolve().parents[1]
RUNT_VERSION = "0.4.1"

# don't satisfy one reachable fork node and a straight-line post-phase
JOINT_DRIVER_UNSUPPORTED = {
    "tests/brave_new_world/signal_asynchrony/signal_async.prot",
    "tests/identities/identity_d0/identity_d0.prot",
    "tests/multi/multi_data/multi_data.prot",
}

GRAPH_INTERP_UNSUPPORTED = {"for_in_loop", "repeat_loop", "tuples"}

# Bounded lowering is prohibitively expensive
# TODO: maybe this should become a dynamically determined
# TODO: property based on trace length/ # of prootocols.
BOUNDED_DRIVER_EXCLUDED = {
    "examples/apb/ch_apb_actual.tx",
    "examples/apb/ip_apb.tx",
    "examples/picorv32/unsigned_mul.tx",
    "examples/wishbone/joint_read_write_long.tx",
    "tests/adders/adder_d1/joint_add_d1_long.tx",
    "tests/adders/adder_d2/joint_add_d2_long.tx",
    "tests/alus/joint_alu_d1_long.tx",
    "tests/alus/joint_alu_d2_long.tx",
    "tests/fpga-debugging/axis-async-fifo-c4/c4_fixed.tx",
    "tests/fpga-debugging/axis-adapter-s3/s3_fixed.tx",
    "tests/multipliers/mult_d2/joint_mul_d2_long.tx",
}


def load_tx_cases() -> list[dict]:
    """Expand the compact catalog rows into the internal field shape.
    This handles default fields which are omitted in the catalog for
    the user experience."""
    out = []
    for path, c in test_catalog.TX_CASES.items():
        out.append(
            {
                "paths": [path],
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
        case = {
            "id": case_id,
            "wave": c.get("wave"),
            "instances": c.get("instances", ()),
            "extra_args": c.get("extra_args", ()),
            "expected": c["expect"],
        }
        if "protocol" in c:
            assert "protocols" not in c
            case["paths"] = [c["protocol"]]
        else:
            case["paths"] = c["protocols"]
        out.append(case)
    return out


# helper function to escape globs in places
def runt_glob_literal(path: str) -> str:
    return path.replace("[", "[[]").replace("*", "[*]").replace("?", "[?]")


def replace_non_alphanumerics(value: object) -> str:
    text = re.sub(r"^-+", "", str(value).strip())
    return re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_") or "default"


def case_stem(case: dict) -> str:
    # Antmicro, Brave New World & APB test cases for the BI share the same
    # `.prot` file but have multiple waveforms, so we use the waveform files'
    # names to identify a particular test, otherwise we use the `.prot` file's stem
    # to identify a test
    wave = case.get("wave")
    if wave and (
        "antmicro" in wave
        or "fpga-debugging" in wave
        or "ethmac" in wave
        or "apb" in wave
    ):
        return Path(wave).stem
    # for all the .wave bi benchmarks, we use the id
    if wave and (wave.endswith(".wave") or "litex" in wave or "wb_stream" in wave):
        return case["id"]
    stem = Path(case["paths"][0]).stem
    return stem.removesuffix(".bi")


def expect_name(case: dict, runner: str) -> str:
    # Each (test, runner) pair is unique, so stem + runner fully identifies the
    # expect file. The runner keeps interp/graph_interp goldens for the same .tx
    # from colliding.
    return f"{replace_non_alphanumerics(case_stem(case))}.{runner}.expect"


def expect_dir(case: dict, _runner: str) -> str:
    base = Path(case["paths"][0]).parent
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
        " ".join(case["paths"]),
    ]
    _tx_tail(cmd, case, with_max_steps=True)
    return [("", repo_root_command(cmd, stderr="stdout"))]


def graph_interp_runt_command(case: dict) -> list[tuple[str, str]]:
    cmd = [*binary_prefix("graph-interp"), "--transactions", " ".join(case["paths"])]
    _tx_tail(cmd, case, with_max_steps=False)

    # These flows lower every protocol in the file, not only the trace's calls.
    if (
        GRAPH_INTERP_UNSUPPORTED & protocol_constructs(case["protocol_path"])
        # Wishbone and FIFO require whole-trace fork semantics.
        or case["paths"][0].startswith("tests/fifo/")
        or case["paths"][0].startswith("tests/wishbone/")
    ):
        flows = [("trace_graph", ["--flow", "trace-graph"])]
    else:
        flows = [
            ("sequential", ["--flow", "sequential"]),
            ("trace_graph", ["--flow", "trace-graph"]),
        ]
    return [(suffix, repo_root_command(cmd + flags)) for suffix, flags in flows]


def bi_runt_command(case: dict) -> list[tuple[str, str]]:
    # We pass in `--color never` to BI to suppress color in error messages
    # (so that the .expect files only display plaintext)
    cmd = [*binary_prefix("bi"), "--color", "never"]
    for p in case["paths"]:
        cmd += ["--protocol", p]
    if case["wave"]:
        cmd += ["--wave", case["wave"]]
    if case["instances"]:
        cmd += ["--instances", *case["instances"]]
    cmd += case["extra_args"]
    # We redirect stderr to stdout so that the expected output files
    # contain error messages if BI fails
    return [("", repo_root_command(cmd, stderr="stdout"))]


def monitor_status_runt_command(case: dict) -> list[tuple[str, str]]:
    common = []
    for path in case["paths"]:
        common += ["--protocol", path]
    common += ["--wave", case["wave"], "--instances", *case["instances"]]
    # Display options affect BI's trace formatting, not monitor acceptance.
    extras = case["extra_args"]
    if "--sample-posedge" in extras:
        index = extras.index("--sample-posedge")
        common += ["--sample-posedge", extras[index + 1]]
    if "--force-x-to-zero" in extras:
        common += ["--force-x-to-zero"]
    return [
        (
            "bi",
            repo_root_command(
                [*binary_prefix("bi"), "--status-only", *common], stderr="inherit"
            ),
        ),
        (
            "system",
            repo_root_command(
                [
                    *binary_prefix("graph-interp"),
                    "--flow",
                    "unbounded-monitor",
                    *common,
                ],
                stderr="inherit",
            ),
        ),
    ]


def waveform_runt_command(case: dict) -> list[tuple[str, str]]:
    ast_cmd = [
        *binary_prefix("protocols-interp"),
        "--color",
        "never",
        "--transactions",
        " ".join(case["paths"]),
        "--ascii-waveform",
    ]
    _tx_tail(ast_cmd, case, with_max_steps=True)

    graph_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        " ".join(case["paths"]),
        "--flow",
        "trace-graph",
        "--ascii-waveform",
    ]
    _tx_tail(graph_cmd, case, with_max_steps=False)

    ts_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        " ".join(case["paths"]),
        "--flow",
        "trace-system",
        "--ascii-waveform",
    ]
    _tx_tail(ts_cmd, case, with_max_steps=False)

    bounded_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        case["paths"][0],
        "--flow",
        "bounded-driver",
        "--bound",
        str(tx_max_trace_protocols(case["paths"][0])),
        "--ascii-waveform",
    ]
    _tx_tail(bounded_cmd, case, with_max_steps=False)

    unbounded_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        " ".join(case["paths"]),
        "--flow",
        "unbounded-driver",
        "--ascii-waveform",
    ]
    _tx_tail(unbounded_cmd, case, with_max_steps=False)

    variants: list[tuple[str, str]] = [
        ("ast", repo_root_command(ast_cmd, stderr="discard")),
        ("graph", repo_root_command(graph_cmd, stderr="discard")),
        ("ts", repo_root_command(ts_cmd, stderr="discard")),
    ]
    if case["protocol_path"] not in JOINT_DRIVER_UNSUPPORTED:
        variants.append(("joint", repo_root_command(unbounded_cmd, stderr="discard")))

    # Expensive or unsupported bounded cases are centralized in the generator.
    if case["paths"][0] not in BOUNDED_DRIVER_EXCLUDED:
        variants.append(("bmc", repo_root_command(bounded_cmd, stderr="discard")))

    return variants


def fail_runt_command(case: dict) -> list[tuple[str, str]]:
    graph_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        " ".join(case["paths"]),
        "--flow",
        "trace-graph",
        "--brief-graph-errors",
    ]
    _tx_tail(graph_cmd, case, with_max_steps=False)

    ts_cmd = [
        *binary_prefix("graph-interp"),
        "--transactions",
        " ".join(case["paths"]),
        "--flow",
        "trace-system",
    ]
    _tx_tail(ts_cmd, case, with_max_steps=False)

    return [
        ("graph", repo_root_command(graph_cmd, stderr="discard")),
        ("ts", repo_root_command(ts_cmd, stderr="discard")),
    ]


@lru_cache(maxsize=None)
def tx_max_trace_protocols(path: str) -> int | None:
    tx_path = REPO_ROOT / path
    if not tx_path.exists():
        return None

    content = tx_path.read_text()
    max_protocols = 0
    for block in re.findall(r"trace\s*{([^}]*)}", content, re.DOTALL):
        protocols = [
            line.strip()
            for line in block.splitlines()
            if line.strip() and not line.strip().startswith("//")
        ]
        max_protocols = max(max_protocols, len(protocols))
    return max_protocols or None


RUNT_BUILDERS = {
    "interp": interp_runt_command,
    "graph_interp": graph_interp_runt_command,
    "bi": bi_runt_command,
    "monitor_status": monitor_status_runt_command,
    "waveform": waveform_runt_command,
    "fail": fail_runt_command,
}


# config generation


@lru_cache(maxsize=None)
def protocol_constructs(
    protocol_path: str, transaction_path: str | None = None
) -> frozenset[str]:
    """
    Constructs used anywhere in a .prot file, via `protocols-cli constructs`.
    """
    command = [
        "cargo",
        "run",
        "-q",
        "--bin",
        "protocols-cli",
        "--",
        "--allow-branch-on-arg",
        "-p",
        protocol_path,
        "constructs",
    ]
    if transaction_path is not None:
        command.extend(["--transactions", transaction_path])
    result = subprocess.run(
        command,
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


def graph_interp_cases(cases: list[dict]) -> list[dict]:
    """Passing tx cases whose protocol uses no for-in or repeat loop."""
    selected = [
        c
        for c in cases
        if c["expected"] == "pass"
        and not GRAPH_INTERP_UNSUPPORTED
        & protocol_constructs(c["protocol_path"], c["paths"][0])
    ]
    # exclude s3 from graph_interp cases
    # TODO: re-include
    selected = [c for c in selected if not c["protocol_path"].endswith("s3.prot")]

    return sorted(selected, key=lambda c: c["paths"][0])


def monitor_status_cases(cases: list[dict]) -> list[dict]:
    """Exclude unsupported loops, argument guards, and guarded-fork composition."""
    return [
        case
        for case in cases
        if "--allow-branch-on-arg" not in case["extra_args"]
        # Contraction creates multiple guarded fork nodes in these protocols.
        # Their parity cases live with the separate guarded-fork implementation.
        and "examples/wishbone/wishbone_pipelined.prot" not in case["paths"]
        and not any(
            {"for_in_loop", "repeat_loop"} & protocol_constructs(path)
            for path in case["paths"]
        )
    ]


def waveform_cases(cases: list[dict]) -> list[dict]:
    """Graph-interpreter cases suitable for cycle-exact comparison."""
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

    return [
        case for case in graph_interp_cases(cases) if case["paths"][0] not in xfailed
    ]


def fail_cases(cases: list[dict]) -> list[dict]:
    """Runtime-failing tx cases whose graph and transition-system waveforms should match."""
    # Stuff like max steps and combinational dependency errors aren't enforced right now.
    runtime_failures = {"assertion_mismatch", "assignment_conflict"}
    graph_interp_unsupported = {"for_in_loop", "repeat_loop"}

    selected = [
        c
        for c in cases
        if c["expected"] in runtime_failures
        and not graph_interp_unsupported & protocol_constructs(c["protocol_path"])
    ]
    return sorted(selected, key=lambda c: c["paths"][0])


def runt_case_suites(suite_name: str, runner: str, cases: list[dict]):
    build = RUNT_BUILDERS[runner]
    suites = []
    for case in sorted(cases, key=lambda c: (c["paths"][0], expect_name(c, runner))):
        path = case["paths"][0]
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
        "monitor_status": ("monitor_status", monitor_status_cases(bi)),
        "graph_interp": ("graph_interp", graph_interp_cases(tx)),
        "waveform": ("waveform", waveform_cases(tx)),
        "fail": ("fail", fail_cases(tx)),
    }

    # A golden may be shared by several flows of the same test, but two
    # different tests sharing one golden is an accidental name collision.
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
