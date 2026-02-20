#!/usr/bin/env python3
"""
Round-trip test: for each passing .tx test, run the interpreter to generate
an FST waveform, then run the monitor on that FST. Reports success/fail counts.

Usage: python scripts/roundtrip.py

TODO: Compare monitor output against original .tx transactions.
"""

import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Optional

PROJECT_ROOT = Path(__file__).resolve().parent.parent


def find_turnt_dir(start: Path) -> Optional[Path]:
    """Walk up from `start` to find the nearest directory containing turnt.toml."""
    d = start
    while d != d.parent:
        if (d / "turnt.toml").exists():
            return d
        d = d.parent
    return None


def parse_arg(args: str, flag: str) -> Optional[str]:
    """Extract value for --flag or --flag=value from an ARGS string."""
    m = re.search(rf"--{flag}[= ](\S+)", args)
    return m.group(1) if m else None


def extract_struct_name(prot_path: Path) -> Optional[str]:
    """Extract the first struct name from a .prot file."""
    m = re.search(r"^struct\s+([A-Za-z_]\w*)", prot_path.read_text(), re.MULTILINE)
    return m.group(1) if m else None


def collect_tx_files() -> list[Path]:
    """Find all .tx files under PROJECT_ROOT, sorted."""
    return sorted(PROJECT_ROOT.rglob("*.tx"))

def collect_generated_fsts(fst_path: Path) -> list[Path]:
    """Collect generated waveform files for one interp run."""
    indexed: list[tuple[int, Path]] = []
    for path in fst_path.parent.glob(f"{fst_path.stem}_*{fst_path.suffix}"):
        suffix = path.stem[len(fst_path.stem) + 1 :]
        if suffix.isdigit():
            indexed.append((int(suffix), path))
    if indexed:
        return [path for _, path in sorted(indexed, key=lambda item: item[0])]
    if fst_path.exists():
        return [fst_path]
    return []


def run_roundtrip():
    passed = 0
    failed = 0
    skipped = 0
    interp_failed = 0
    failed_entries: list[tuple[str, str]] = []
    interp_failed_files: list[str] = []

    for tx_file in collect_tx_files():
        tx_rel = str(tx_file.relative_to(PROJECT_ROOT))
        text = tx_file.read_text()

        # Parse // ARGS: line
        args_match = re.search(r"^// ARGS:\s*(.+)$", text, re.MULTILINE)
        if not args_match:
            skipped += 1
            continue
        args = args_match.group(1)

        # Skip error tests (non-zero RETURN code)
        return_match = re.search(r"^// RETURN:\s*(\d+)", text, re.MULTILINE)
        if return_match and int(return_match.group(1)) != 0:
            skipped += 1
            continue

        # Extract --protocol and --verilog paths
        prot_rel = parse_arg(args, "protocol")
        verilog_rel = parse_arg(args, "verilog")
        if not prot_rel or not verilog_rel:
            skipped += 1
            continue

        # ARGS paths are relative to the nearest turnt.toml directory
        base_dir = find_turnt_dir(tx_file.parent)
        if not base_dir:
            skipped += 1
            continue

        prot_file = base_dir / prot_rel
        if not prot_file.exists():
            skipped += 1
            continue

        # Extract struct name from .prot file
        struct_name = extract_struct_name(prot_file)
        if not struct_name:
            skipped += 1
            continue

        # Instance name: --module if specified, otherwise verilog filename stem
        module_name = parse_arg(args, "module")
        instance_name = module_name if module_name else Path(verilog_rel).stem

        # Step 1: Run interpreter to generate FST
        # We pass a base .fst path; interp may write either that exact file
        # or indexed files like *_0.fst for multi-trace input.
        fd, fst_file = tempfile.mkstemp(suffix=".fst")
        os.close(fd)
        os.unlink(fst_file)
        fst_path = Path(fst_file)

        try:
            interp_cmd = (
                f"cargo run --quiet --package protocols-interp -- "
                f"--color never --transactions {tx_file} {args} --fst {fst_file}"
            )
            result = subprocess.run(
                interp_cmd, shell=True, cwd=base_dir,
                capture_output=True, text=True,
            )
            if result.returncode != 0:
                interp_failed += 1
                interp_failed_files.append(tx_rel)
                continue

            generated_fsts = collect_generated_fsts(fst_path)
            if not generated_fsts:
                failed += 1
                failed_entries.append(
                    (tx_rel, f"No waveform file generated at {fst_path} or indexed variants")
                )
                continue

            # Step 2: Run monitor on each generated FST (one per trace)
            for trace_idx, generated_fst in enumerate(generated_fsts):
                monitor_cmd = (
                    f"cargo run --quiet --package protocols-monitor -- "
                    f"-p {prot_file} --wave {generated_fst} "
                    f"--instances {instance_name}:{struct_name}"
                )
                result = subprocess.run(
                    monitor_cmd, shell=True, cwd=base_dir,
                    capture_output=True, text=True,
                )
                if result.returncode == 0:
                    passed += 1
                else:
                    failed += 1
                    output = (result.stdout + result.stderr).strip()
                    failed_entries.append((f"{tx_rel} (trace {trace_idx})", output))
        finally:
            for path in fst_path.parent.glob(f"{fst_path.stem}_*{fst_path.suffix}"):
                try:
                    path.unlink()
                except OSError:
                    pass
            try:
                fst_path.unlink()
            except OSError:
                pass

    # Print results
    total = passed + failed
    print()
    print("=== Round-trip results ===")
    print(f"  Passed:  {passed} / {total}")
    print(f"  Failed:  {failed} / {total}")
    print(f"  Skipped: {skipped} (transactions don't complete successfully)")
    if interp_failed:
        print(f"  Interpreter failures: {interp_failed}")

    if interp_failed_files:
        print()
        print("Interpreter failures (unexpected — these should be passing tests):")
        for f in interp_failed_files:
            print(f"  - {f}")

    if failed_entries:
        print()
        print("Monitor failures:")
        for file, output in failed_entries:
            print()
            print(f"  --- {file} ---")
            for line in output.splitlines():
                print(f"  {line}")


if __name__ == "__main__":
    run_roundtrip()
