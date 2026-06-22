#!/usr/bin/env python3
"""
Benchmarks the monitor on a range of test files using Hyperfine
(measuring CPU wall-clock time, averaged over 10 runs) and
creates a CSV with the results.
"""

# Note: before running this script, first run
# `cargo build --release --package protocols-monitor`

import csv
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from tqdm import tqdm

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_catalog  # noqa: E402

OUTPUT_CSV = "benchmark_results/benchmark_results.csv"


def main():
    cases = sorted(
        test_catalog.MONITOR_CASES.values(),
        key=lambda case: (case["path"], case["id"]),
    )

    if not cases:
        print("No monitor cases found in scripts/test_catalog.py")
        return

    rows = []

    for case in tqdm(cases, desc="Benchmarking", unit="case"):
        # By default, Hyperfine executes the monitor for at least 10
        # times on each test file
        cmd = [
            "hyperfine",
            # Disable shell startup to avoid noise in measurements
            "--shell=none",
            "--export-json",
            "tmp_hyperfine.json",
            # Five warmup runs to run benchmarks on warm cache & avoid
            # outliers between runs
            "--warmup",
            "5",
            # Suppress hyperfine output (results are checked separately)
            "--style",
            "none",
            # Ignore non-zero exit codes (some tests are expected to fail)
            "--ignore-failure",
            # Run the monitor directly on the catalog case.
            " ".join(monitor_command(case)),
        ]

        # Suppress monitor output to avoid measurement overhead
        subprocess.run(
            cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )

        # Load hyperfine JSON
        with open("tmp_hyperfine.json") as f:
            data = json.load(f)

        result = data["results"][0]
        mean_time = result["mean"]
        stddev = result["stddev"]
        min_time = result["min"]
        max_time = result["max"]

        # Read the number of steps from the .prof file
        prof_file = profile_path(case)
        if not os.path.exists(prof_file):
            # Skip tests without .prof files (e.g., tests expected to fail)
            continue

        # Parse lines beginning with "No. of steps taken..." and extract the integer
        # Example: "No. of steps taken by AxisFifo scheduler: 74" -> 74
        num_steps = None
        pattern = re.compile(r"^No\. of steps taken.*:\s*(\d+)")

        with open(prof_file) as f:
            for line in f:
                match = pattern.match(line)
                if match:
                    num_steps = int(match.group(1))
                    break  # Use the first matching line

        if num_steps is None:
            # Skip if no step count found
            continue

        # Normalize times by number of steps
        mean_time_per_step = mean_time / num_steps
        stddev_per_step = stddev / num_steps
        min_time_per_step = min_time / num_steps
        max_time_per_step = max_time / num_steps

        # Compute throughput (steps per second)
        steps_per_sec = 1.0 / mean_time_per_step

        base = os.path.basename(case["path"])
        if base.endswith(".prot"):
            base = base[:-5]  # strip .prot

        rows.append(
            [
                case["path"],
                base,
                num_steps,
                mean_time_per_step,
                stddev_per_step,
                min_time_per_step,
                max_time_per_step,
                steps_per_sec,
            ]
        )

    # ---- Write CSV ----
    os.makedirs(os.path.dirname(OUTPUT_CSV), exist_ok=True)
    with open(OUTPUT_CSV, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "file_path",
                "test_name",
                "num_steps",
                "mean_per_step",
                "stddev_per_step",
                "min_per_step",
                "max_per_step",
                "steps_per_sec",
            ]
        )
        writer.writerows(rows)

    print(f"\nWrote results to {OUTPUT_CSV}")


def monitor_command(case):
    cmd = ["cargo", "monitor", "--protocol", case["path"]]
    if case["wave"]:
        cmd += ["--wave", case["wave"]]
    if case["instances"]:
        cmd += ["--instances", *case["instances"]]
    cmd += case["extra_args"]
    return cmd


def profile_path(case):
    candidates = [Path(case["path"]).with_suffix(".prof")]
    wave = case.get("wave")
    if isinstance(wave, str):
        candidates.append(Path(wave).with_suffix(".prof"))
    for candidate in candidates:
        if candidate.exists():
            return str(candidate)
    return str(candidates[0])


if __name__ == "__main__":
    main()
