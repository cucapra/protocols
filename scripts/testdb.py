#!/usr/bin/env python3
"""Derived test catalog for Protocols snapshot tests.

This is a migration layer: it reads the current test metadata from
test files and snapshots, then exposes protocol- and case-oriented rows that
generated Runt configs can use as their source of truth.
"""

from __future__ import annotations

import argparse
import json
import os
import pprint
import re
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Optional


REPO_ROOT = Path(__file__).resolve().parents[1]
TEST_ROOT = Path("tests")
TEST_ROOTS = (TEST_ROOT, Path("examples"))
MONITOR_ROOT = TEST_ROOT
RUNT_VERSION = "0.4.1"


@dataclass(frozen=True)
class Protocol:
    id: str
    path: str
    root: str
    family: str
    features: tuple[str, ...]


@dataclass(frozen=True)
class TxCase:
    id: str
    path: str
    protocol_id: Optional[str]
    protocol_path: Optional[str]
    verilog: tuple[str, ...]
    module: Optional[str]
    max_steps: Optional[int]
    extra_args: tuple[str, ...]
    expected_return: int
    expected: str
    failure_class: Optional[str]
    failure_message: Optional[str]
    trace_count: int
    transactions: tuple[str, ...]
    properties: tuple[str, ...]


@dataclass(frozen=True)
class MonitorCase:
    id: str
    path: str
    protocol_id: str
    wave: Optional[str]
    instances: tuple[str, ...]
    max_steps: Optional[int]
    timeout_secs: Optional[int]
    extra_args: tuple[str, ...]
    expected_return: int
    expected: str
    failure_class: Optional[str]
    failure_message: Optional[str]
    properties: tuple[str, ...]


@dataclass
class TestDatabase:
    protocols: dict[str, Protocol] = field(default_factory=dict)
    tx_cases: dict[str, TxCase] = field(default_factory=dict)
    monitor_cases: dict[str, MonitorCase] = field(default_factory=dict)
    protocols_by_path: dict[str, str] = field(default_factory=dict)

    def protocol_for_path(self, path: Optional[str]) -> Optional[Protocol]:
        if path is None:
            return None
        protocol_id = self.protocols_by_path.get(path)
        return self.protocols.get(protocol_id) if protocol_id else None

    def tx_where(
        self,
        *,
        expected: Optional[str] = None,
        failure_class: Optional[str] = None,
        exclude_failure_class: Optional[str] = None,
        under: Optional[str] = None,
        feature: Optional[str] = None,
    ) -> list[TxCase]:
        cases = list(self.tx_cases.values())
        if expected:
            cases = [case for case in cases if case.expected == expected]
        if failure_class:
            cases = [case for case in cases if case.failure_class == failure_class]
        if exclude_failure_class:
            cases = [
                case for case in cases if case.failure_class != exclude_failure_class
            ]
        if under:
            prefix = normalize_rel_path(under).rstrip("/") + "/"
            cases = [
                case
                for case in cases
                if case.path == prefix[:-1] or case.path.startswith(prefix)
            ]
        if feature:
            cases = [
                case
                for case in cases
                if case.protocol_id
                and feature in self.protocols[case.protocol_id].features
            ]
        return sorted(cases, key=lambda case: case.path)


def normalize_rel_path(path: str | Path, base_dir: Path = REPO_ROOT) -> str:
    raw = Path(path)
    if raw.is_absolute():
        raw = raw.resolve()
        try:
            raw = raw.relative_to(base_dir)
        except ValueError:
            return raw.as_posix()
    return raw.as_posix()


def path_id(path: Path) -> str:
    return normalize_rel_path(path.with_suffix("")).replace("/", ".")


def path_family(path: Path) -> str:
    rel = Path(normalize_rel_path(path))
    parts = rel.parts
    if len(parts) >= 2 and parts[0] == "tests":
        return parts[1]
    if len(parts) >= 2 and parts[0] == "examples":
        return parts[1]
    return parts[0] if parts else "unknown"


def path_root(path: Path) -> str:
    rel = Path(normalize_rel_path(path))
    if rel.parts and rel.parts[0] == "tests":
        return "tests"
    if rel.parts and rel.parts[0] == "examples":
        return "examples"
    return "."


def parse_comment_value(text: str, key: str) -> Optional[str]:
    match = re.search(rf"^//\s*{re.escape(key)}:\s*(.+)$", text, re.MULTILINE)
    return match.group(1).strip() if match else None


def parse_expected_return(text: str) -> int:
    value = parse_comment_value(text, "RETURN")
    return int(value) if value is not None else 0


def parse_timeout_secs(text: str) -> Optional[int]:
    cmd = parse_comment_value(text, "CMD")
    if cmd is None:
        return None
    match = re.match(r"timeout\s+(\d+)s\b", cmd)
    return int(match.group(1)) if match else None


def parse_cli_args(args: Optional[str]) -> dict[str, object]:
    """Parse the subset of CLI syntax used by current test metadata."""
    result: dict[str, object] = {
        "verilog": [],
        "protocol": None,
        "module": None,
        "max_steps": None,
        "wave": None,
        "instances": [],
        "raw": args or "",
        "flags": [],
    }
    if not args:
        return result

    tokens = shlex.split(args)
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if not token.startswith("--"):
            cast_list(result["flags"]).append(token)
            i += 1
            continue

        name_value = token[2:].split("=", 1)
        name = name_value[0].replace("-", "_")
        inline_value = name_value[1] if len(name_value) == 2 else None

        if name == "verilog":
            values, i = consume_multi_value(tokens, i, inline_value)
            cast_list(result["verilog"]).extend(values)
        elif name == "instances":
            values, i = consume_multi_value(tokens, i, inline_value)
            cast_list(result["instances"]).extend(values)
        elif name in {"protocol", "module", "max_steps", "wave"}:
            value, i = consume_single_value(tokens, i, inline_value)
            result[name] = value
        else:
            cast_list(result["flags"]).append(token)
            i += 1
    return result


def consume_single_value(
    tokens: list[str], index: int, inline_value: Optional[str]
) -> tuple[Optional[str], int]:
    if inline_value is not None:
        return inline_value, index + 1
    next_index = index + 1
    if next_index < len(tokens) and not tokens[next_index].startswith("--"):
        return tokens[next_index], next_index + 1
    return None, index + 1


def consume_multi_value(
    tokens: list[str], index: int, inline_value: Optional[str]
) -> tuple[list[str], int]:
    if inline_value is not None:
        return [inline_value], index + 1
    values: list[str] = []
    index += 1
    while index < len(tokens) and not tokens[index].startswith("--"):
        values.append(tokens[index])
        index += 1
    return values, index


def cast_list(value: object) -> list[str]:
    assert isinstance(value, list)
    return value


def resolve_arg_path(base: Path, value: Optional[str]) -> Optional[str]:
    if value is None:
        return None
    return normalize_rel_path((base / value).resolve())


def resolve_arg_paths(base: Path, values: Iterable[str]) -> tuple[str, ...]:
    return tuple(resolve_arg_path(base, value) or value for value in values)


def turnt_base_for_path(path: Path) -> Path:
    current = path.parent
    while current != current.parent:
        if (current / "turnt.toml").exists():
            return current
        current = current.parent
    return path.parent


def args_base_for_path(path: Path) -> Path:
    rel = Path(normalize_rel_path(path))
    if rel.parts and rel.parts[0] == "tests":
        return REPO_ROOT / "tests"
    if rel.parts and rel.parts[0] == "examples":
        return REPO_ROOT / "examples"
    return turnt_base_for_path(path)


def infer_protocol_features(path: Path) -> tuple[str, ...]:
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return ()

    features = set()
    patterns = {
        "assertions": r"\bassert_eq\s*\(",
        "conditionals": r"\bif\s*\(",
        "while": r"\bwhile\s*\(",
        "repeat": r"\brepeat\b",
        "for_in": r"\bfor\s+",
        "fork": r"\bfork\s*\(",
        "idle": r"#\[\s*idle\s*\]",
        "dont_care": r"\bX\b",
        "comb_dependency": r"combinational|combdep",
    }
    for name, pattern in patterns.items():
        if re.search(pattern, text):
            features.add(name)
    if len(re.findall(r"^\s*prot\s+", text, re.MULTILINE)) > 1:
        features.add("multi_protocol")
    return tuple(sorted(features))


def parse_trace_count(text: str) -> int:
    return len(re.findall(r"^\s*trace\s*\{", text, re.MULTILINE))


def parse_transactions(text: str) -> tuple[str, ...]:
    names = []
    for match in re.finditer(r"^\s*([A-Za-z_]\w*)\s*\(", text, re.MULTILINE):
        name = match.group(1)
        if name != "trace":
            names.append(name)
    return tuple(sorted(set(names)))


def first_error_message(snapshot_path: Path) -> Optional[str]:
    if not snapshot_path.exists():
        return None
    for line in snapshot_path.read_text(errors="replace").splitlines():
        if line.startswith("error:"):
            return line.removeprefix("error:").strip()
    return None


def infer_failure_class(message: Optional[str]) -> Optional[str]:
    if message is None:
        return None

    checks = (
        (
            "comb_dependency",
            (
                "depends on input(s)",
                "Cannot assign to forbidden input",
                "combinationally dependent",
            ),
        ),
        ("assertion_mismatch", ("did not evaluate to the same value",)),
        ("assignment_conflict", ("attempted conflicting assignment",)),
        (
            "fork_protocol_error",
            (
                "attempted to fork more than once",
                "called `fork()` before calling `step()`",
                "wasn't `step()`",
            ),
        ),
        (
            "static_type_error",
            ("Type mismatch", "Invalid slice operation"),
        ),
        (
            "static_well_formedness",
            ("conditions in if-statements / while-loops cannot mention",),
        ),
        ("max_steps", ("Reached the maximum number of steps",)),
    )
    for failure_class, needles in checks:
        if any(needle in message for needle in needles):
            return failure_class
    return "unknown"


def infer_case_properties(path: Path, expected: str, trace_count: int) -> tuple[str, ...]:
    rel = normalize_rel_path(path)
    name = path.stem
    properties = {expected}
    if trace_count > 1:
        properties.add("multi_trace")
    if "bug" in name or "/bug" in rel or "_bug" in rel:
        properties.add("bug")
    if "fix" in name or "/fix" in rel or "_fix" in rel or "fixed" in rel:
        properties.add("fix")
    return tuple(sorted(properties))


def discover_protocols(db: TestDatabase) -> None:
    for root in dict.fromkeys((*TEST_ROOTS, MONITOR_ROOT)):
        for path in sorted((REPO_ROOT / root).rglob("*.prot")):
            protocol = Protocol(
                id=path_id(path),
                path=normalize_rel_path(path),
                root=path_root(path),
                family=path_family(path),
                features=infer_protocol_features(path),
            )
            db.protocols[protocol.id] = protocol
            db.protocols_by_path[protocol.path] = protocol.id


def discover_tx_cases(db: TestDatabase) -> None:
    for root in TEST_ROOTS:
        for path in sorted((REPO_ROOT / root).rglob("*.tx")):
            text = path.read_text(errors="replace")
            args = parse_cli_args(parse_comment_value(text, "ARGS"))
            base = args_base_for_path(path)
            protocol_path = resolve_arg_path(base, as_optional_str(args["protocol"]))
            protocol = db.protocol_for_path(protocol_path)
            expected_return = parse_expected_return(text)
            expected = "pass" if expected_return == 0 else "fail"
            message = first_error_message(path.with_suffix(".out"))
            trace_count = parse_trace_count(text)
            case = TxCase(
                id=path_id(path),
                path=normalize_rel_path(path),
                protocol_id=protocol.id if protocol else None,
                protocol_path=protocol_path,
                verilog=resolve_arg_paths(base, cast_list(args["verilog"])),
                module=as_optional_str(args["module"]),
                max_steps=as_optional_int(args["max_steps"]),
                extra_args=tuple(cast_list(args["flags"])),
                expected_return=expected_return,
                expected=expected,
                failure_class=infer_failure_class(message) if expected == "fail" else None,
                failure_message=message,
                trace_count=trace_count,
                transactions=parse_transactions(text),
                properties=infer_case_properties(path, expected, trace_count),
            )
            db.tx_cases[case.id] = case


def discover_monitor_cases(db: TestDatabase) -> None:
    for path in sorted((REPO_ROOT / MONITOR_ROOT).rglob("*.prot")):
        text = path.read_text(errors="replace")
        args = parse_cli_args(parse_comment_value(text, "ARGS"))
        base = args_base_for_path(path)
        instances = tuple(cast_list(args["instances"]))
        if not instances:
            continue
        expected_return = parse_expected_return(text)
        expected = "pass" if expected_return == 0 else "fail"
        message = first_error_message(path.with_suffix(".out"))
        protocol_id = db.protocols_by_path[normalize_rel_path(path)]
        case = MonitorCase(
            id=path_id(path),
            path=normalize_rel_path(path),
            protocol_id=protocol_id,
            wave=resolve_arg_path(base, as_optional_str(args["wave"])),
            instances=instances,
            max_steps=as_optional_int(args["max_steps"]),
            timeout_secs=parse_timeout_secs(text),
            extra_args=tuple(cast_list(args["flags"])),
            expected_return=expected_return,
            expected=expected,
            failure_class=infer_failure_class(message) if expected == "fail" else None,
            failure_message=message,
            properties=infer_case_properties(path, expected, 0),
        )
        db.monitor_cases[case.id] = case


def as_optional_str(value: object) -> Optional[str]:
    return value if isinstance(value, str) else None


def as_optional_int(value: object) -> Optional[int]:
    if isinstance(value, str):
        return int(value)
    return None


def load_database() -> TestDatabase:
    db = TestDatabase()
    discover_protocols(db)
    discover_tx_cases(db)
    discover_monitor_cases(db)
    return db


def load_catalog_dict() -> dict[str, dict[str, dict[str, object]]]:
    try:
        import test_catalog

        return {
            "protocols": test_catalog.PROTOCOLS,
            "tx_cases": test_catalog.TX_CASES,
            "monitor_cases": test_catalog.MONITOR_CASES,
        }
    except ModuleNotFoundError:
        db = load_database()
        return catalog_payload(db)


def load_catalog_database() -> TestDatabase:
    catalog = load_catalog_dict()
    db = TestDatabase()
    for key, row in sorted(catalog["protocols"].items()):
        protocol = Protocol(
            id=as_str(row["id"]),
            path=as_str(row["path"]),
            root=as_str(row["root"]),
            family=as_str(row["family"]),
            features=tuple(as_str_list(row["features"])),
        )
        db.protocols[key] = protocol
        db.protocols_by_path[protocol.path] = key
    for key, row in sorted(catalog["tx_cases"].items()):
        db.tx_cases[key] = TxCase(
            id=as_str(row["id"]),
            path=as_str(row["path"]),
            protocol_id=optional_str(row["protocol_id"]),
            protocol_path=optional_str(row["protocol_path"]),
            verilog=tuple(as_str_list(row["verilog"])),
            module=optional_str(row["module"]),
            max_steps=optional_int(row["max_steps"]),
            extra_args=tuple(as_str_list(row["extra_args"])),
            expected_return=required_int(row["expected_return"]),
            expected=as_str(row["expected"]),
            failure_class=optional_str(row["failure_class"]),
            failure_message=optional_str(row["failure_message"]),
            trace_count=required_int(row["trace_count"]),
            transactions=tuple(as_str_list(row["transactions"])),
            properties=tuple(as_str_list(row["properties"])),
        )
    for key, row in sorted(catalog["monitor_cases"].items()):
        db.monitor_cases[key] = MonitorCase(
            id=as_str(row["id"]),
            path=as_str(row["path"]),
            protocol_id=as_str(row["protocol_id"]),
            wave=optional_str(row["wave"]),
            instances=tuple(as_str_list(row["instances"])),
            max_steps=optional_int(row["max_steps"]),
            timeout_secs=optional_int(row["timeout_secs"]),
            extra_args=tuple(as_str_list(row["extra_args"])),
            expected_return=required_int(row["expected_return"]),
            expected=as_str(row["expected"]),
            failure_class=optional_str(row["failure_class"]),
            failure_message=optional_str(row["failure_message"]),
            properties=tuple(as_str_list(row["properties"])),
        )
    return db


def json_default(value: object) -> object:
    if isinstance(value, TestDatabase):
        return {
            "protocols": value.protocols,
            "tx_cases": value.tx_cases,
            "monitor_cases": value.monitor_cases,
        }
    if hasattr(value, "__dataclass_fields__"):
        return asdict(value)
    raise TypeError(f"cannot serialize {type(value).__name__}")


def catalog_payload(db: TestDatabase) -> dict[str, object]:
    return {
        "protocols": {
            key: asdict(value) for key, value in sorted(db.protocols.items())
        },
        "tx_cases": {
            key: asdict(value) for key, value in sorted(db.tx_cases.items())
        },
        "monitor_cases": {
            key: asdict(value) for key, value in sorted(db.monitor_cases.items())
        },
    }


def cast_catalog_table(value: object) -> dict[str, dict[str, object]]:
    assert isinstance(value, dict)
    return value


def split_antmicro_monitor_cases(
    cases: dict[str, dict[str, object]],
) -> tuple[dict[str, dict[str, object]], list[str]]:
    explicit = {}
    antmicro_stems = []
    common_extra_args = [
        "--sample-posedge",
        "tb.dut.clk",
        "--show-waveform-time",
        "--time-unit",
        "ns",
    ]
    for key, case in sorted(cases.items()):
        wave = optional_str(case["wave"])
        match = re.fullmatch(r"tests/antmicro/(.+)\.fst", wave or "")
        if (
            match
            and case["expected"] == "pass"
            and case["expected_return"] == 0
            and as_str_list(case["extra_args"]) == common_extra_args
            and case["failure_class"] is None
            and case["failure_message"] is None
            and as_str_list(case["instances"]) == ["tb.dut:WBSubordinate"]
            and case["max_steps"] is None
            and case["timeout_secs"] is None
            and as_str_list(case["properties"]) == ["pass"]
            and case["id"] == key
            and as_str(case["path"])
            in {
                f"tests/antmicro/{match.group(1)}.prot",
                "tests/antmicro/wishbone_subordinate.prot",
            }
            and as_str(case["protocol_id"])
            in {key, "tests.antmicro.wishbone_subordinate"}
        ):
            antmicro_stems.append(match.group(1))
        else:
            explicit[key] = case
    return explicit, antmicro_stems


def antmicro_stems_expr(stems: list[str]) -> str:
    expected = (
        [f"fifo_classic/test_fifo_classic_{i}" for i in range(1, 9)]
        + [f"fifo_constant/test_fifo_constant_{i}" for i in range(1, 9)]
        + [
            f"sram_classic/test_sram_classic_{width}_{offset}"
            for width in (16, 1, 2, 4, 8)
            for offset in (0, 12, 4, 8)
        ]
        + [
            f"sram_incrementing/test_sram_incrementing_{width}_{offset}_{index}"
            for width in (16, 1, 2, 4, 8)
            for offset in (0, 12, 4, 8)
            for index in range(4)
        ]
    )
    if stems != expected:
        return pprint.pformat(stems, width=88)
    return (
        "(\n"
        '    [f"fifo_classic/test_fifo_classic_{i}" for i in range(1, 9)]\n'
        '    + [f"fifo_constant/test_fifo_constant_{i}" for i in range(1, 9)]\n'
        "    + [\n"
        '        f"sram_classic/test_sram_classic_{width}_{offset}"\n'
        "        for width in (16, 1, 2, 4, 8)\n"
        "        for offset in (0, 12, 4, 8)\n"
        "    ]\n"
        "    + [\n"
        '        f"sram_incrementing/test_sram_incrementing_{width}_{offset}_{index}"\n'
        "        for width in (16, 1, 2, 4, 8)\n"
        "        for offset in (0, 12, 4, 8)\n"
        "        for index in range(4)\n"
        "    ]\n"
        ")"
    )


def write_python_catalog(db: TestDatabase, output_path: Path) -> None:
    payload = catalog_payload(db)
    monitor_cases, antmicro_stems = split_antmicro_monitor_cases(
        cast_catalog_table(payload["monitor_cases"])
    )
    text = (
        "# Checked-in test catalog.\n"
        "# Regenerate normalized formatting with scripts/testdb.py generate-catalog.\n\n"
        "ANTMICRO_EXTRA_ARGS = [\n"
        '    "--sample-posedge",\n'
        '    "tb.dut.clk",\n'
        '    "--show-waveform-time",\n'
        '    "--time-unit",\n'
        '    "ns",\n'
        "]\n\n"
        'ANTMICRO_PROTOCOL = "tests/antmicro/wishbone_subordinate.prot"\n'
        'ANTMICRO_PROTOCOL_ID = "tests.antmicro.wishbone_subordinate"\n\n'
        f"ANTMICRO_TRACE_STEMS = {antmicro_stems_expr(antmicro_stems)}\n\n"
        "def _antmicro_monitor_case(stem):\n"
        '    case_id = f"tests.antmicro.{stem.replace(\'/\', \'.\')}"\n'
        "    return {\n"
        '        "expected": "pass",\n'
        '        "expected_return": 0,\n'
        '        "extra_args": ANTMICRO_EXTRA_ARGS,\n'
        '        "failure_class": None,\n'
        '        "failure_message": None,\n'
        '        "id": case_id,\n'
        '        "instances": ["tb.dut:WBSubordinate"],\n'
        '        "max_steps": None,\n'
        '        "path": ANTMICRO_PROTOCOL,\n'
        '        "properties": ["pass"],\n'
        '        "protocol_id": ANTMICRO_PROTOCOL_ID,\n'
        '        "timeout_secs": None,\n'
        '        "wave": f"tests/antmicro/{stem}.fst",\n'
        "    }\n\n"
        f"PROTOCOLS = {pprint.pformat(payload['protocols'], width=88)}\n\n"
        f"TX_CASES = {pprint.pformat(payload['tx_cases'], width=88)}\n\n"
        f"MONITOR_CASES = {pprint.pformat(monitor_cases, width=88)}\n\n"
        "for _stem in ANTMICRO_TRACE_STEMS:\n"
        "    _case = _antmicro_monitor_case(_stem)\n"
        '    MONITOR_CASES[_case["id"]] = _case\n'
        "\n"
        "CATALOG = {\n"
        '    "protocols": PROTOCOLS,\n'
        '    "tx_cases": TX_CASES,\n'
        '    "monitor_cases": MONITOR_CASES,\n'
        "}\n"
    )
    output_path.write_text(text)


def rel_from(path: str | Path, base_dir: Path) -> str:
    return Path(normalize_rel_path(path)).resolve().relative_to(REPO_ROOT).as_posix()


def runt_rel_path(path: str | Path, config_dir: Path) -> str:
    absolute = (REPO_ROOT / normalize_rel_path(path)).resolve()
    return os.path.relpath(absolute, config_dir.resolve())


def toml_string(value: str) -> str:
    return json.dumps(value)


def runt_glob_literal(path: str) -> str:
    return path.replace("[", "[[]").replace("*", "[*]").replace("?", "[?]")


def slug(value: object) -> str:
    text = str(value).strip()
    text = re.sub(r"^-+", "", text)
    text = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_")
    return text or "default"


def flag_profile(args: Iterable[str]) -> list[str]:
    tokens = list(args)
    profile = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token.startswith("--"):
            name = token.removeprefix("--")
            if i + 1 < len(tokens) and not tokens[i + 1].startswith("--"):
                profile.append(f"{name}_{tokens[i + 1]}")
                i += 2
            else:
                profile.append(name)
                i += 1
        else:
            profile.append(token)
            i += 1
    return [slug(part) for part in profile]


def tx_profile(case: dict[str, object]) -> str:
    parts = []
    protocol = optional_str(case["protocol_path"])
    if protocol:
        parts.append(Path(protocol).stem)
    module = optional_str(case["module"])
    if module and slug(module) not in {slug(part) for part in parts}:
        parts.append(module)
    max_steps = optional_int(case["max_steps"])
    if max_steps is not None:
        parts.append(f"max{max_steps}")
    parts.extend(flag_profile(as_str_list(case["extra_args"])))
    return ".".join(slug(part) for part in parts) or "default"


def monitor_profile(case: dict[str, object]) -> str:
    test_stem = case_stem(case)
    parts = []
    wave = optional_str(case["wave"])
    if wave and Path(wave).stem != test_stem:
        parts.append(Path(wave).stem)
    for instance in as_str_list(case["instances"]):
        parts.append(instance.rsplit(":", 1)[-1])
    max_steps = optional_int(case.get("max_steps"))
    if max_steps is not None:
        parts.append(f"max{max_steps}")
    timeout_secs = optional_int(case.get("timeout_secs"))
    if timeout_secs is not None:
        parts.append(f"timeout{timeout_secs}s")
    return ".".join(slug(part) for part in parts) or "default"


def case_stem(case: dict[str, object]) -> str:
    wave = optional_str(case.get("wave"))
    if wave and as_str(case["path"]).startswith("tests/antmicro/"):
        return Path(wave).stem
    stem = Path(as_str(case["path"])).stem
    if stem.endswith(".monitor"):
        return stem[: -len(".monitor")]
    return stem


def expect_dir_for_case(case: dict[str, object], runner: str, config_dir: Path) -> str:
    if runner == "monitor":
        wave = optional_str(case.get("wave"))
        test_dir = Path(wave).parent / "expects" if wave else Path(as_str(case["path"])).parent / "expects"
    else:
        test_dir = Path(as_str(case["path"])).parent / "expects"
    return runt_rel_path(test_dir, config_dir)


def expect_name_for_case(case: dict[str, object], runner: str) -> str:
    stem = case_stem(case)
    profile = monitor_profile(case) if runner == "monitor" else tx_profile(case)
    return ".".join([slug(stem), slug(runner), profile, "expect"])


def write_runt_toml(
    output_dir: Path,
    suites: list[tuple[str, str, str, str, str]],
) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    chunks = [f"ver = {toml_string(RUNT_VERSION)}\n"]
    for name, expect_dir, expect_name, cmd, path in suites:
        chunks.append("[[tests]]")
        chunks.append(f"name = {toml_string(name)}")
        chunks.append("paths = [")
        chunks.append(f"  {toml_string(runt_glob_literal(runt_rel_path(path, output_dir)))},")
        chunks.append("]")
        chunks.append(f"expect_dir = {toml_string(expect_dir)}")
        chunks.append(f"expect_name = {toml_string(expect_name)}")
        chunks.append(f"cmd = {toml_string(cmd)}")
        chunks.append("")
    (output_dir / "runt.toml").write_text("\n".join(chunks))


def cargo_run_prefix(config_dir: Path, package: str) -> list[str]:
    return [
        "cargo",
        "run",
        "--manifest-path",
        "Cargo.toml",
        "--quiet",
        "--offline",
        "--package",
        package,
        "--",
    ]


def case_path_for_cmd(path: Optional[str], config_dir: Path) -> Optional[str]:
    return normalize_rel_path(path) if path else None


def repo_root_command(cmd: list[str], placeholder_arg: str) -> str:
    quoted = shlex.join(cmd).replace(shlex.quote(placeholder_arg), '"$TEST"')
    return "TEST='{}'; TEST=${TEST#../../}; cd ../.. && " + quoted + " 2>/dev/null"


def timeout_cmd(timeout_secs: int, cmd: list[str]) -> list[str]:
    script = (
        "import os, signal, subprocess, sys; "
        "timeout=float(sys.argv[1]); "
        "proc=subprocess.Popen(sys.argv[2:], start_new_session=True); "
        "\ntry:\n"
        "    sys.exit(proc.wait(timeout=timeout))\n"
        "except subprocess.TimeoutExpired:\n"
        "    os.killpg(proc.pid, signal.SIGTERM)\n"
        "    try:\n"
        "        proc.wait(timeout=1)\n"
        "    except subprocess.TimeoutExpired:\n"
        "        os.killpg(proc.pid, signal.SIGKILL)\n"
        "    sys.exit(124)\n"
    )
    return ["python3", "-c", script, str(timeout_secs), *cmd]


def interp_runt_command(case: dict[str, object], config_dir: Path) -> str:
    placeholder = "__RUNT_TEST_PATH__"
    cmd = [
        *cargo_run_prefix(config_dir, "protocols-interp"),
        "--color",
        "never",
        "--transactions",
        placeholder,
    ]
    cmd.extend(as_str_list(case["extra_args"]))
    verilog = [normalize_rel_path(path) for path in as_str_list(case["verilog"])]
    if verilog:
        cmd.extend(["--verilog", *verilog])
    protocol = case_path_for_cmd(optional_str(case["protocol_path"]), config_dir)
    if protocol:
        cmd.extend(["--protocol", protocol])
    module = optional_str(case["module"])
    if module:
        cmd.extend(["--module", module])
    max_steps = optional_int(case["max_steps"])
    if max_steps is not None:
        cmd.extend(["--max-steps", str(max_steps)])
    return repo_root_command(cmd, placeholder)


def graph_interp_runt_command(case: dict[str, object], config_dir: Path) -> str:
    placeholder = "__RUNT_TEST_PATH__"
    cmd = [
        *cargo_run_prefix(config_dir, "graph-interp"),
        "--transactions",
        placeholder,
    ]
    cmd.extend(as_str_list(case["extra_args"]))
    verilog = [normalize_rel_path(path) for path in as_str_list(case["verilog"])]
    if verilog:
        cmd.extend(["--verilog", *verilog])
    protocol = case_path_for_cmd(optional_str(case["protocol_path"]), config_dir)
    if protocol:
        cmd.extend(["--protocol", protocol])
    module = optional_str(case["module"])
    if module:
        cmd.extend(["--module", module])
    return repo_root_command(cmd, placeholder)


def monitor_runt_command(case: dict[str, object], config_dir: Path) -> str:
    placeholder = "__RUNT_TEST_PATH__"
    cmd = [
        *cargo_run_prefix(config_dir, "protocols-monitor"),
        "--protocol",
        placeholder,
    ]
    wave = case_path_for_cmd(optional_str(case["wave"]), config_dir)
    if wave:
        cmd.extend(["--wave", wave])
    instances = as_str_list(case["instances"])
    if instances:
        cmd.extend(["--instances", *instances])
    max_steps = optional_int(case.get("max_steps"))
    if max_steps is not None:
        cmd.extend(["--max-steps", str(max_steps)])
    cmd.extend(as_str_list(case["extra_args"]))
    timeout_secs = optional_int(case.get("timeout_secs"))
    if timeout_secs is not None:
        cmd = timeout_cmd(timeout_secs, cmd)
    return repo_root_command(cmd, placeholder)


def runt_case_suites(
    suite_name: str,
    runner: str,
    cases: list[dict[str, object]],
    config_dir: Path,
) -> list[tuple[str, str, str, str, str]]:
    suites = []
    for case in sorted(
        cases,
        key=lambda item: (as_str(item["path"]), expect_name_for_case(item, runner)),
    ):
        if runner == "interp":
            cmd = interp_runt_command(case, config_dir)
        elif runner == "graph_interp":
            cmd = graph_interp_runt_command(case, config_dir)
        elif runner == "monitor":
            cmd = monitor_runt_command(case, config_dir)
        else:
            raise ValueError(f"unknown runner {runner}")
        path = as_str(case["path"])
        expect_name = expect_name_for_case(case, runner)
        name = (
            f"{suite_name}."
            f"{slug(Path(path).with_suffix('').as_posix())}."
            f"{slug(Path(expect_name).with_suffix('').as_posix())}"
        )
        suites.append(
            (
                name,
                expect_dir_for_case(case, runner, config_dir),
                expect_name,
                cmd,
                path,
            )
        )
    return suites


def tx_cases_where(
    cases: Iterable[dict[str, object]],
    *,
    under: Optional[str] = None,
    paths: Optional[set[str]] = None,
) -> list[dict[str, object]]:
    selected = list(cases)
    if under is not None:
        prefix = normalize_rel_path(under).rstrip("/") + "/"
        selected = [
            case
            for case in selected
            if as_str(case["path"]) == prefix[:-1]
            or as_str(case["path"]).startswith(prefix)
        ]
    if paths is not None:
        selected = [case for case in selected if as_str(case["path"]) in paths]
    return sorted(selected, key=lambda case: as_str(case["path"]))


def monitor_cases_where(
    cases: Iterable[dict[str, object]], *, under: Optional[str] = None
) -> list[dict[str, object]]:
    selected = list(cases)
    if under is not None:
        prefix = normalize_rel_path(under).rstrip("/") + "/"
        selected = [
            case
            for case in selected
            if as_str(case["path"]) == prefix[:-1]
            or as_str(case["path"]).startswith(prefix)
        ]
    return sorted(selected, key=lambda case: as_str(case["path"]))


def graph_interp_paths() -> set[str]:
    allowlist = REPO_ROOT / "tests/graph_interp_allowlist.txt"
    if not allowlist.exists():
        return set()
    return {
        normalize_rel_path(line.strip())
        for line in allowlist.read_text().splitlines()
        if line.strip()
    }


def generate_runt_configs(catalog: dict[str, dict[str, dict[str, object]]]) -> None:
    tx_cases = list(catalog["tx_cases"].values())
    monitor_cases = list(catalog["monitor_cases"].values())
    expect_commands: dict[str, str] = {}

    suite_specs = {
        "interp": [("interp", "interp", tx_cases_where(tx_cases))],
        "monitor": [("monitor", "monitor", monitor_cases_where(monitor_cases))],
        "bnw_monitor": [
            (
                "bnw_monitor",
                "monitor",
                monitor_cases_where(monitor_cases, under="tests/fpga-debugging"),
            )
        ],
        "francis_bnw_monitor": [
            (
                "francis_bnw_monitor",
                "monitor",
                monitor_cases_where(
                    monitor_cases, under="tests/brave_new_world_francis"
                ),
            )
        ],
        "axis": [
            (
                "axis",
                "monitor",
                monitor_cases_where(monitor_cases, under="tests/wal/advanced"),
            )
        ],
        "adders": [
            ("adders", "interp", tx_cases_where(tx_cases, under="tests/adders"))
        ],
        "graph_interp": [
            (
                "graph_interp",
                "graph_interp",
                tx_cases_where(tx_cases, paths=graph_interp_paths()),
            )
        ],
        "alus": [("alus", "interp", tx_cases_where(tx_cases, under="tests/alus"))],
        "identities": [
            (
                "identities",
                "interp",
                tx_cases_where(tx_cases, under="tests/identities"),
            )
        ],
        "multi": [
            ("multi", "interp", tx_cases_where(tx_cases, under="tests/multi"))
        ],
        "picorv": [
            ("picorv", "interp", tx_cases_where(tx_cases, under="examples/picorv32"))
        ],
    }
    suite_specs["turnt"] = [
        ("interp", "interp", tx_cases_where(tx_cases)),
        ("monitor", "monitor", monitor_cases_where(monitor_cases)),
    ]

    for suite_name, suites in suite_specs.items():
        config_dir = REPO_ROOT / "runt" / suite_name
        runt_suites = []
        for name, runner, cases in suites:
            runt_suites.extend(runt_case_suites(name, runner, cases, config_dir))
        for _name, expect_dir, expect_name, cmd, _path in runt_suites:
            expect_path = (config_dir / expect_dir / expect_name).resolve().as_posix()
            prior_cmd = expect_commands.setdefault(expect_path, cmd)
            if prior_cmd != cmd:
                raise SystemExit(
                    "expectation name collision for "
                    f"{normalize_rel_path(expect_path)}"
                )
        write_runt_toml(config_dir, runt_suites)


def cmd_generate_runt(_db: TestDatabase, _args: argparse.Namespace) -> int:
    catalog = load_catalog_dict()
    generate_runt_configs(catalog)
    print("wrote runt/*/runt.toml")
    return 0


def protocol_index(db: TestDatabase) -> list[dict[str, object]]:
    rows = []
    tx_by_protocol: dict[str, list[str]] = {}
    monitor_by_protocol: dict[str, list[str]] = {}
    for case in db.tx_cases.values():
        if case.protocol_id:
            tx_by_protocol.setdefault(case.protocol_id, []).append(case.id)
    for case in db.monitor_cases.values():
        monitor_by_protocol.setdefault(case.protocol_id, []).append(case.id)

    for protocol in sorted(db.protocols.values(), key=lambda item: item.path):
        row = asdict(protocol)
        row["tx_cases"] = sorted(tx_by_protocol.get(protocol.id, []))
        row["monitor_cases"] = sorted(monitor_by_protocol.get(protocol.id, []))
        rows.append(row)
    return rows


def cmd_stats(db: TestDatabase, _args: argparse.Namespace) -> int:
    print(f"protocols: {len(db.protocols)}")
    print(f"tx_cases: {len(db.tx_cases)}")
    print(f"monitor_cases: {len(db.monitor_cases)}")
    print("")
    print("tx expected:")
    print_counts(case.expected for case in db.tx_cases.values())
    print("")
    print("tx failure_class:")
    print_counts(
        case.failure_class or "none"
        for case in db.tx_cases.values()
        if case.expected == "fail"
    )
    return 0


def print_counts(values: Iterable[str]) -> None:
    counts: dict[str, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    for key, value in sorted(counts.items()):
        print(f"  {key}: {value}")


def cmd_dump(db: TestDatabase, args: argparse.Namespace) -> int:
    if args.table == "all":
        payload: object = db
    elif args.table == "protocol-index":
        payload = protocol_index(db)
    elif args.table == "protocols":
        payload = list(db.protocols.values())
    elif args.table == "tx":
        payload = list(db.tx_cases.values())
    else:
        payload = list(db.monitor_cases.values())
    print(json.dumps(payload, default=json_default, indent=2, sort_keys=True))
    return 0


def cmd_generate_catalog(db: TestDatabase, args: argparse.Namespace) -> int:
    output_path = (REPO_ROOT / args.output).resolve()
    write_python_catalog(db, output_path)
    print(f"wrote {normalize_rel_path(output_path)}")
    print(
        f"protocols={len(db.protocols)} "
        f"tx_cases={len(db.tx_cases)} "
        f"monitor_cases={len(db.monitor_cases)}"
    )
    return 0


def normalize_case_path(path: str) -> str:
    raw = Path(path)
    absolute = raw if raw.is_absolute() else (Path.cwd() / raw)
    try:
        return absolute.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return normalize_rel_path(path)


def as_str(value: object) -> str:
    assert isinstance(value, str)
    return value


def as_str_list(value: object) -> list[str]:
    assert isinstance(value, (list, tuple))
    return [as_str(item) for item in value]


def optional_str(value: object) -> Optional[str]:
    return value if isinstance(value, str) else None


def optional_int(value: object) -> Optional[int]:
    return value if isinstance(value, int) else None


def required_int(value: object) -> int:
    assert isinstance(value, int)
    return value


def find_case_by_path(
    cases: dict[str, dict[str, object]], path: str
) -> dict[str, object]:
    if path in cases:
        return cases[path]
    normalized = normalize_case_path(path)
    matches = [case for case in cases.values() if case["path"] == normalized]
    if len(matches) != 1:
        raise SystemExit(f"expected one catalog case for {normalized}, found {len(matches)}")
    return matches[0]


def interp_command(case: dict[str, object]) -> list[str]:
    cmd = [
        "cargo",
        "interp",
        "--color",
        "never",
        "--transactions",
        as_str(case["path"]),
    ]
    cmd.extend(as_str_list(case["extra_args"]))
    verilog = as_str_list(case["verilog"])
    if verilog:
        cmd.extend(["--verilog", *verilog])
    protocol = optional_str(case["protocol_path"])
    if protocol:
        cmd.extend(["--protocol", protocol])
    module = optional_str(case["module"])
    if module:
        cmd.extend(["--module", module])
    max_steps = optional_int(case["max_steps"])
    if max_steps is not None:
        cmd.extend(["--max-steps", str(max_steps)])
    return cmd


def graph_interp_command(case: dict[str, object]) -> list[str]:
    cmd = [
        "cargo",
        "run",
        "-q",
        "-p",
        "graph-interp",
        "--",
        "--transactions",
        as_str(case["path"]),
    ]
    cmd.extend(as_str_list(case["extra_args"]))
    verilog = as_str_list(case["verilog"])
    if verilog:
        cmd.extend(["--verilog", *verilog])
    protocol = optional_str(case["protocol_path"])
    if protocol:
        cmd.extend(["--protocol", protocol])
    module = optional_str(case["module"])
    if module:
        cmd.extend(["--module", module])
    return cmd


def monitor_command(case: dict[str, object]) -> list[str]:
    cmd = ["cargo", "monitor", "--protocol", as_str(case["path"])]
    wave = optional_str(case["wave"])
    if wave:
        cmd.extend(["--wave", wave])
    instances = as_str_list(case["instances"])
    if instances:
        cmd.extend(["--instances", *instances])
    cmd.extend(as_str_list(case["extra_args"]))
    return cmd


def run_case_command(cmd: list[str]) -> int:
    completed = subprocess.run(cmd, cwd=REPO_ROOT, text=False)
    return completed.returncode


def cmd_exec(_db: TestDatabase, args: argparse.Namespace) -> int:
    catalog = load_catalog_dict()
    if args.runner in {"interp", "graph_interp"}:
        case = find_case_by_path(catalog["tx_cases"], args.path)
        cmd = interp_command(case) if args.runner == "interp" else graph_interp_command(case)
    elif args.runner == "monitor":
        case = find_case_by_path(catalog["monitor_cases"], args.path)
        cmd = monitor_command(case)
    else:
        raise SystemExit(f"unknown runner: {args.runner}")

    if args.print_command:
        print(shlex.join(cmd))
        return 0
    return run_case_command(cmd)


def cmd_list_tx(db: TestDatabase, args: argparse.Namespace) -> int:
    for case in db.tx_where(
        expected=args.expected,
        failure_class=args.failure_class,
        exclude_failure_class=args.exclude_failure_class,
        under=args.under,
        feature=args.feature,
    ):
        fields = [case.path, case.expected]
        if case.failure_class:
            fields.append(case.failure_class)
        if case.protocol_id:
            fields.append(case.protocol_id)
        print("\t".join(fields))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    stats = subparsers.add_parser("stats", help="Summarize catalog rows")
    stats.set_defaults(needs_db=True)
    stats.set_defaults(func=cmd_stats)

    dump = subparsers.add_parser("dump", help="Dump catalog rows as JSON")
    dump.add_argument(
        "table",
        choices=("all", "protocols", "protocol-index", "tx", "monitor"),
        nargs="?",
        default="all",
    )
    dump.set_defaults(func=cmd_dump)
    dump.set_defaults(needs_db=True)

    generate = subparsers.add_parser(
        "generate-catalog", help="Rewrite the checked-in catalog Python module"
    )
    generate.add_argument("output", nargs="?", default="scripts/test_catalog.py")
    generate.set_defaults(needs_db=True)
    generate.set_defaults(func=cmd_generate_catalog)

    generate_runt = subparsers.add_parser(
        "generate-runt", help="Write checked-in runt.toml configs from the catalog"
    )
    generate_runt.set_defaults(needs_db=False)
    generate_runt.set_defaults(func=cmd_generate_runt)

    exec_parser = subparsers.add_parser(
        "exec", help="Execute one catalog case for a runt suite"
    )
    exec_parser.add_argument("runner", choices=("interp", "graph_interp", "monitor"))
    exec_parser.add_argument("path")
    exec_parser.add_argument("--print-command", action="store_true")
    exec_parser.set_defaults(needs_db=False)
    exec_parser.set_defaults(func=cmd_exec)

    list_tx = subparsers.add_parser("list-tx", help="List selected tx cases")
    list_tx.add_argument("--expected", choices=("pass", "fail"))
    list_tx.add_argument("--failure-class")
    list_tx.add_argument("--exclude-failure-class")
    list_tx.add_argument("--under")
    list_tx.add_argument("--feature")
    list_tx.set_defaults(needs_db=True)
    list_tx.set_defaults(func=cmd_list_tx)

    return parser


def main() -> int:
    args = build_parser().parse_args()
    db = load_catalog_database() if args.needs_db else TestDatabase()
    return args.func(db, args)


if __name__ == "__main__":
    raise SystemExit(main())
