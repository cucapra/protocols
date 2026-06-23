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


def load_monitor_cases() -> list[dict]:
    """Same idea as load_tx_cases but for the monitor cases
    """
    out = []
    for case_id, c in test_catalog.MONITOR_CASES.items():
        out.append(
            {
                "id": case_id,
                "path": c["protocol"],
                "wave": c.get("wave"),
                "instances": c.get("instances", ()),
                "max_steps": c.get("max_steps"),
                "timeout_secs": c.get("timeout_secs"),
                "extra_args": c.get("extra_args", ()),
                "expected": c["expect"],
            }
        )
    return out

# helper function to escape globs in places
def runt_glob_literal(path: str) -> str:
    return path.replace("[", "[[]").replace("*", "[*]").replace("?", "[?]")

# kinda convoluted set of methods to find a good .expect file name
def replace_non_alphanumerics(value: object) -> str:
    text = re.sub(r"^-+", "", str(value).strip())
    return re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_") or "default"

def flag_profile(args: list[str]) -> list[str]:
    profile = []
    i = 0
    while i < len(args):
        token = args[i]
        if (
            token.startswith("--")
            and i + 1 < len(args)
            and not args[i + 1].startswith("--")
        ):
            profile.append(f"{token[2:]}_{args[i + 1]}")
            i += 2
        else:
            profile.append(token.removeprefix("--"))
            i += 1
    return [replace_non_alphanumerics(part) for part in profile]


def case_stem(case: dict) -> str:
    wave = case.get("wave")
    if wave and case["path"].startswith("tests/antmicro/"):
        return Path(wave).stem
    stem = Path(case["path"]).stem
    return stem.removesuffix(".monitor")


def tx_profile(case: dict) -> str:
    parts = []
    if case["protocol_path"]:
        parts.append(Path(case["protocol_path"]).stem)
    if case["module"] and replace_non_alphanumerics(case["module"]) not in {replace_non_alphanumerics(p) for p in parts}:
        parts.append(case["module"])
    if case["max_steps"] is not None:
        parts.append(f"max{case['max_steps']}")
    parts += flag_profile(list(case["extra_args"]))
    return ".".join(replace_non_alphanumerics(p) for p in parts) or "default"


def monitor_profile(case: dict) -> str:
    parts = []
    if case["wave"] and Path(case["wave"]).stem != case_stem(case):
        parts.append(Path(case["wave"]).stem)
    parts += [inst.rsplit(":", 1)[-1] for inst in case["instances"]]
    if case["max_steps"] is not None:
        parts.append(f"max{case['max_steps']}")
    if case["timeout_secs"] is not None:
        parts.append(f"timeout{case['timeout_secs']}s")
    return ".".join(replace_non_alphanumerics(p) for p in parts) or "default"


def expect_name(case: dict, runner: str) -> str:
    profile = monitor_profile(case) if runner == "monitor" else tx_profile(case)
    return ".".join([replace_non_alphanumerics(case_stem(case)), replace_non_alphanumerics(runner), profile, "expect"])


def expect_dir(case: dict, runner: str) -> str:
    wave = case.get("wave")
    base = Path(wave if runner == "monitor" and wave else case["path"]).parent
    return f"../../{base.as_posix()}/expects"


# command construction

def cargo_prefix(package: str) -> list[str]:
    return [
        "cargo",
        "run",
        "--offline",
        "--package",
        package,
        "--",
    ]


def repo_root_command(cmd: list[str]) -> str:
    # Each runt test runs exactly one path, so we bake it straight into the
    return "cd ../.. && " + shlex.join(cmd) + " 2>/dev/null"


def timeout_cmd(timeout_secs: int, cmd: list[str]) -> list[str]:
    # Runt doesn't support expected timeouts, so we have to have this wrapper
    # on the interp/monitor commands
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


def interp_runt_command(case: dict) -> str:
    cmd = [
        *cargo_prefix("protocols-interp"),
        "--color",
        "never",
        "--transactions",
        case["path"],
    ]
    _tx_tail(cmd, case, with_max_steps=True)
    return repo_root_command(cmd)


def graph_interp_runt_command(case: dict) -> str:
    cmd = [*cargo_prefix("graph-interp"), "--transactions", case["path"]]
    _tx_tail(cmd, case, with_max_steps=False)
    return repo_root_command(cmd)


def monitor_runt_command(case: dict) -> str:
    cmd = [*cargo_prefix("protocols-monitor"), "--protocol", case["path"]]
    if case["wave"]:
        cmd += ["--wave", case["wave"]]
    if case["instances"]:
        cmd += ["--instances", *case["instances"]]
    if case["max_steps"] is not None:
        cmd += ["--max-steps", str(case["max_steps"])]
    cmd += case["extra_args"]
    if case["timeout_secs"] is not None:
        cmd = timeout_cmd(case["timeout_secs"], cmd)
    return repo_root_command(cmd)


RUNT_BUILDERS = {
    "interp": interp_runt_command,
    "graph_interp": graph_interp_runt_command,
    "monitor": monitor_runt_command,
}


# config generation


def cases_where(cases, under=None) -> list[dict]:
    selected = [c for c in cases if under is None or c["path"].startswith(under + "/")]
    return sorted(selected, key=lambda c: c["path"])


# Loop constructs the graph interpreter cannot handle (AST construct names).
GRAPH_INTERP_UNSUPPORTED = {"for_in_loop", "repeat_loop"}


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


def graph_interp_cases(cases: list[dict]) -> list[dict]:
    """Passing tx cases whose protocol uses no for-in or repeat loop."""
    selected = [
        c
        for c in cases
        if c["expected"] == "pass"
        and not GRAPH_INTERP_UNSUPPORTED & protocol_constructs(c["protocol_path"])
    ]
    return sorted(selected, key=lambda c: c["path"])


def runt_case_suites(suite_name: str, runner: str, cases: list[dict]):
    build = RUNT_BUILDERS[runner]
    suites = []
    for case in sorted(cases, key=lambda c: (c["path"], expect_name(c, runner))):
        path = case["path"]
        name = (
            f"{suite_name}.{replace_non_alphanumerics(Path(path).with_suffix('').as_posix())}"
            f".{replace_non_alphanumerics(expect_name(case, runner).removesuffix('.expect'))}"
        )
        suites.append(
            (
                name,
                expect_dir(case, runner),
                expect_name(case, runner),
                build(case),
                path,
            )
        )
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
    mon = load_monitor_cases()
    interp_dirs = {
        "adders": "tests/adders",
        "alus": "tests/alus",
        "identities": "tests/identities",
        "multi": "tests/multi",
        "picorv": "examples/picorv32",
    }
    monitor_dirs = {
        "bnw_monitor": "tests/fpga-debugging",
        "francis_bnw_monitor": "tests/brave_new_world_francis",
        "axis": "tests/wal/advanced",
    }
    suite_specs = {
        "interp": [("interp", "interp", cases_where(tx))],
        "monitor": [("monitor", "monitor", cases_where(mon))],
        **{
            n: [(n, "monitor", cases_where(mon, under=d))]
            for n, d in monitor_dirs.items()
        },
        "graph_interp": [
            ("graph_interp", "graph_interp", graph_interp_cases(tx)),
        ],
        **{
            n: [(n, "interp", cases_where(tx, under=d))] for n, d in interp_dirs.items()
        },
        "turnt": [
            ("interp", "interp", cases_where(tx)),
            ("monitor", "monitor", cases_where(mon)),
        ],
    }

    expect_commands: dict[str, str] = {}
    for suite_name, suites in suite_specs.items():
        config_dir = REPO_ROOT / "runt" / suite_name
        runt_suites = []
        for name, runner, cases in suites:
            runt_suites += runt_case_suites(name, runner, cases)
        for _name, edir, ename, cmd, _path in runt_suites:
            expect_path = (config_dir / edir / ename).resolve().as_posix()
            if expect_commands.setdefault(expect_path, cmd) != cmd:
                raise SystemExit(f"expectation name collision for {expect_path}")
        write_runt_toml(config_dir, runt_suites)


def main() -> int:
    generate_runt_configs()
    print("wrote runt/*/runt.toml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
