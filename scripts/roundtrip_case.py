#!/usr/bin/env python3
"""Run one roundtrip check for a single .tx file.

Usage:
  uv run scripts/roundtrip_case.py path/to/test.tx
"""

import argparse
import re
import subprocess
import traceback
from pathlib import Path
from typing import Optional


def parse_arg(args: str, flag: str) -> Optional[str]:
    """Extract a CLI flag value from a // ARGS line."""
    m = re.search(rf"--{flag}[= ](\S+)", args)
    return m.group(1) if m else None


def relpath_str(path: Path, base_dir: Path) -> str:
    """Return a path string relative to base_dir when possible."""
    try:
        return str(path.relative_to(base_dir))
    except ValueError:
        return str(path)


def sanitize_error_output(text: str) -> str:
    """Remove unstable runtime panic location lines from stderr/stdout text."""
    lines = []
    for line in text.splitlines():
        if "panicked at " in line:
            continue
        lines.append(line)
    sanitized = "\n".join(lines).strip()
    return sanitized


def extract_struct_name(prot_path: Path) -> Optional[str]:
    """Return the first struct name declared in a .prot file."""
    m = re.search(r"^struct\s+([A-Za-z_]\w*)", prot_path.read_text(), re.MULTILINE)
    return m.group(1) if m else None


def normalize_trace_line(line: str) -> str:
    """Normalize one trace statement line for stable expected/actual comparison."""
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
    """Parse `trace { ... }` blocks and return normalized statements per trace."""
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
    """Collect generated FSTs for a run, preferring indexed multi-trace outputs."""
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
    """Delete base and indexed temporary waveform files created for a test case."""
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
    """Print a failure message and return success for Turnt."""
    print(msg)
    return 0


def format_trace(trace: list[str]) -> str:
    """Format one trace block for output."""
    if not trace:
        return "<empty trace>"
    return "\n".join(trace)


def format_trace_block(trace: list[str]) -> str:
    """Format one trace using `trace { ... }` syntax with statement indentation."""
    if not trace:
        return "trace {\n}"
    indented = "\n".join(f"    {stmt}" for stmt in trace)
    return f"trace {{\n{indented}\n}}"


def tx_path_to_wave_stem(tx_file: Path, base_dir: Path) -> str:
    """Build a deterministic wave stem from the tx path."""
    try:
        rel = tx_file.relative_to(base_dir)
        rel_no_suffix = rel.with_suffix("")
        stem = str(rel_no_suffix).replace("/", "-").replace("\\", "-")
    except ValueError:
        stem = tx_file.stem
    # Keep filenames portable and deterministic.
    return re.sub(r"[^A-Za-z0-9._-]", "-", stem)


def format_monitor_trace_candidates(traces: list[list[str]]) -> str:
    """Format parsed monitor traces as indexed candidates."""
    if not traces:
        return "<none>"
    chunks = []
    for i, t in enumerate(traces):
        chunks.append(f"candidate_monitor_trace: {i}\n{format_trace_block(t)}")
    return "\n\n".join(chunks)


def main() -> int:
    """Execute one roundtrip check for a single `.tx` file."""
    parser = argparse.ArgumentParser(
        description="Run one roundtrip check for a single .tx file."
    )
    parser.add_argument("tx_file", help="Path to the .tx file to check")
    parser.add_argument(
        "--keep-fst",
        action="store_true",
        help="Do not delete the intermediate .fst waveform file after the check",
    )
    args_ns = parser.parse_args()

    tx_file = Path(args_ns.tx_file).resolve()
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

    tx_file_rel = relpath_str(tx_file, base_dir)
    prot_file_rel = relpath_str(prot_file, base_dir)

    module_name = parse_arg(args, "module")
    instance_name = module_name if module_name else Path(verilog_rel).stem
    expected_traces = parse_trace_blocks(tx_text)
    wave_stem = tx_path_to_wave_stem(tx_file, base_dir)
    roundtrip_tmp_dir = base_dir / ".roundtrip_tmp"
    roundtrip_tmp_dir.mkdir(parents=True, exist_ok=True)
    fst_path = roundtrip_tmp_dir / f"{wave_stem}.fst"
    fst_path_rel = relpath_str(fst_path, base_dir)
    cleanup_generated_fsts(fst_path)

    try:
        interp_cmd = (
            "cargo run --quiet --package protocols-interp -- "
            f"--color never --transactions {tx_file_rel} {args} --fst {fst_path_rel}"
        )
        interp = subprocess.run(
            interp_cmd,
            shell=True,
            cwd=base_dir,
            capture_output=True,
            text=True,
        )
        if interp.returncode != 0:
            output = sanitize_error_output((interp.stdout + interp.stderr).strip())
            return fail(
                f"interpreter_error:\n{output if output else '<no interpreter output>'}"
            )

        generated_fsts = collect_generated_fsts(fst_path)
        if not generated_fsts:
            return fail("interpreter_error:\nNo waveform file generated by interpreter")

        printed_blocks = 0

        for trace_idx, generated_fst in enumerate(generated_fsts):
            if printed_blocks > 0:
                print("")
                print("---")
                print("")
            print(f"trace_block: {trace_idx}")
            print(f"fst_file: {relpath_str(generated_fst, base_dir)}")
            printed_blocks += 1
            if trace_idx >= len(expected_traces):
                print("trace_result: FAIL")
                print("failure_kind: extra_interpreter_trace")
                print("message:")
                print(
                    f"Interpreter generated unexpected extra trace {trace_idx} for {tx_file}"
                )
                print("")
                continue

            monitor_cmd = (
                "cargo run --quiet --package protocols-monitor -- "
                f"-p {prot_file_rel} --wave {relpath_str(generated_fst, base_dir)} "
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
                output = sanitize_error_output(
                    (monitor.stdout + monitor.stderr).strip()
                )
                print("trace_result: FAIL")
                print("failure_kind: monitor_error")
                print("interpreter_trace:")
                print(format_trace_block(expected_traces[trace_idx]))
                print("")
                print("monitor_error:")
                print(output if output else "<no monitor output>")
                print("")
                continue

            monitor_traces = parse_trace_blocks(monitor.stdout)
            expected = expected_traces[trace_idx]
            matched_idx = next(
                (
                    i
                    for i, candidate in enumerate(monitor_traces)
                    if candidate == expected
                ),
                None,
            )
            if matched_idx is None:
                print("trace_result: FAIL")
                print("failure_kind: trace_mismatch")
                print("interpreter_trace:")
                print(format_trace_block(expected))
                print("")
                print("parsed_monitor_trace_candidates:")
                print(format_monitor_trace_candidates(monitor_traces))
                print("")
                continue

            print("trace_result: PASS")
            print(f"matched_monitor_trace_index: {matched_idx}")
            print("interpreter_trace:")
            print(format_trace_block(expected))
            print("")
            print("parsed_monitor_trace_candidates:")
            print(format_monitor_trace_candidates(monitor_traces))
            print("")

        if len(generated_fsts) < len(expected_traces):
            for trace_idx in range(len(generated_fsts), len(expected_traces)):
                if printed_blocks > 0:
                    print("")
                    print("---")
                    print("")
                print(f"trace_block: {trace_idx}")
                printed_blocks += 1
                print("trace_result: FAIL")
                print("failure_kind: missing_interpreter_trace")
                print("interpreter_trace:")
                print(format_trace_block(expected_traces[trace_idx]))
                print("")

        return 0
    finally:
        if not args_ns.keep_fst:
            cleanup_generated_fsts(fst_path)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception:
        print(f"roundtrip_tester_error:\n{traceback.format_exc().strip()}")
        raise SystemExit(0)
