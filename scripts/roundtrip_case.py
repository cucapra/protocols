#!/usr/bin/env python3
"""Run one roundtrip check for a single .tx file.

Usage:
  uv run scripts/roundtrip_case.py path/to/test.tx
"""

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Optional


def parse_arg(args: str, flag: str) -> Optional[str]:
    m = re.search(rf"--{flag}[= ](\S+)", args)
    return m.group(1) if m else None


def extract_struct_name(prot_path: Path) -> Optional[str]:
    m = re.search(r"^struct\s+([A-Za-z_]\w*)", prot_path.read_text(), re.MULTILINE)
    return m.group(1) if m else None


def normalize_trace_line(line: str) -> str:
    line = line.strip()
    if "//" in line:
        line = line.split("//", 1)[0].rstrip()
    if not line:
        return line

    m = re.fullmatch(r"([A-Za-z_]\w*)\s*\((.*)\)\s*;?", line)
    if not m:
        return line

    fn_name = m.group(1)
    args_blob = m.group(2).strip()
    if not args_blob:
        return f"{fn_name}();"

    normalized_args = []
    for raw_arg in args_blob.split(","):
        arg = raw_arg.strip().replace("_", "")
        if re.fullmatch(r"0[bB][01]+", arg):
            normalized_args.append(str(int(arg[2:], 2)))
        elif re.fullmatch(r"0[xX][0-9a-fA-F]+", arg):
            normalized_args.append(str(int(arg[2:], 16)))
        elif re.fullmatch(r"\d+", arg):
            normalized_args.append(str(int(arg, 10)))
        else:
            normalized_args.append(arg)

    return f"{fn_name}({', '.join(normalized_args)});"


def parse_trace_blocks(text: str) -> list[list[str]]:
    traces: list[list[str]] = []
    in_trace = False
    current: list[str] = []

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not in_trace:
            if line == "trace {":
                in_trace = True
                current = []
            continue

        if line == "}":
            traces.append(current)
            in_trace = False
            current = []
            continue

        normalized = normalize_trace_line(raw_line)
        if normalized:
            current.append(normalized)

    return traces


def collect_generated_fsts(base_fst: Path) -> list[Path]:
    indexed: list[tuple[int, Path]] = []
    for path in base_fst.parent.glob(f"{base_fst.stem}_*{base_fst.suffix}"):
        suffix = path.stem[len(base_fst.stem) + 1 :]
        if suffix.isdigit():
            indexed.append((int(suffix), path))

    if indexed:
        return [path for _, path in sorted(indexed, key=lambda item: item[0])]
    if base_fst.exists():
        return [base_fst]
    return []


def cleanup_generated_fsts(base_fst: Path) -> None:
    for path in base_fst.parent.glob(f"{base_fst.stem}_*{base_fst.suffix}"):
        try:
            path.unlink()
        except OSError:
            pass
    try:
        base_fst.unlink()
    except OSError:
        pass


def fail(msg: str) -> int:
    print(msg)
    return 1


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: roundtrip_case.py <tx_file>")
        return 2

    tx_file = Path(sys.argv[1]).resolve()
    if not tx_file.exists():
        return fail(f"Missing tx file: {tx_file}")

    tx_text = tx_file.read_text()
    args_match = re.search(r"^// ARGS:\s*(.+)$", tx_text, re.MULTILINE)
    if not args_match:
        print("SKIP: missing // ARGS")
        return 0
    args = args_match.group(1)

    return_match = re.search(r"^// RETURN:\s*(\d+)", tx_text, re.MULTILINE)
    if return_match and int(return_match.group(1)) != 0:
        print("SKIP: non-zero // RETURN")
        return 0

    prot_rel = parse_arg(args, "protocol")
    verilog_rel = parse_arg(args, "verilog")
    if not prot_rel or not verilog_rel:
        print("SKIP: missing --protocol or --verilog in // ARGS")
        return 0

    base_dir = tx_file.parent
    while base_dir != base_dir.parent and not (base_dir / "turnt.toml").exists():
        base_dir = base_dir.parent
    if not (base_dir / "turnt.toml").exists():
        return fail(f"No turnt.toml found for {tx_file}")

    prot_file = (base_dir / prot_rel).resolve()
    if not prot_file.exists():
        return fail(f"Missing protocol file: {prot_file}")

    struct_name = extract_struct_name(prot_file)
    if not struct_name:
        return fail(f"Could not find struct in protocol: {prot_file}")

    module_name = parse_arg(args, "module")
    instance_name = module_name if module_name else Path(verilog_rel).stem
    expected_traces = parse_trace_blocks(tx_text)

    fd, fst_file = tempfile.mkstemp(suffix=".fst")
    os.close(fd)
    os.unlink(fst_file)
    fst_path = Path(fst_file)

    try:
        interp_cmd = (
            "cargo run --quiet --package protocols-interp -- "
            f"--color never --transactions {tx_file} {args} --fst {fst_file}"
        )
        interp = subprocess.run(
            interp_cmd,
            shell=True,
            cwd=base_dir,
            capture_output=True,
            text=True,
        )
        if interp.returncode != 0:
            return fail("Interpreter failed during roundtrip generation")

        generated_fsts = collect_generated_fsts(fst_path)
        if not generated_fsts:
            return fail("No waveform file generated by interpreter")

        for trace_idx, generated_fst in enumerate(generated_fsts):
            if trace_idx >= len(expected_traces):
                return fail(
                    f"Interpreter generated unexpected extra trace {trace_idx} for {tx_file}"
                )

            monitor_cmd = (
                "cargo run --quiet --package protocols-monitor -- "
                f"-p {prot_file} --wave {generated_fst} "
                f"--instances {instance_name}:{struct_name}"
            )
            monitor = subprocess.run(
                monitor_cmd,
                shell=True,
                cwd=base_dir,
                capture_output=True,
                text=True,
            )
            if monitor.returncode != 0:
                output = (monitor.stdout + monitor.stderr).strip()
                return fail(
                    f"Monitor failed for trace {trace_idx} in {tx_file}\n{output}"
                )

            monitor_traces = parse_trace_blocks(monitor.stdout)
            expected = expected_traces[trace_idx]
            if expected not in monitor_traces:
                expected_dump = "\n".join(expected) or "<empty trace>"
                observed_dump = (
                    "\n\n".join(
                        f"trace {i}:\n" + ("\n".join(t) if t else "<empty trace>")
                        for i, t in enumerate(monitor_traces)
                    )
                    if monitor_traces
                    else "<no traces parsed from monitor stdout>"
                )
                return fail(
                    f"Trace mismatch for {tx_file} trace {trace_idx}\n"
                    f"Expected:\n{expected_dump}\n\nObserved:\n{observed_dump}"
                )

            print(f"Roundtrip trace {trace_idx} executed successfully!")

        if len(generated_fsts) < len(expected_traces):
            return fail(
                f"Interpreter generated only {len(generated_fsts)} traces, "
                f"but source has {len(expected_traces)}"
            )

        return 0
    finally:
        cleanup_generated_fsts(fst_path)


if __name__ == "__main__":
    raise SystemExit(main())
