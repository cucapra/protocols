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
import re
import subprocess
import glob
import os
from tqdm import tqdm

TEST_ROOT = "monitor/tests"
OUTPUT_CSV = "benchmark_results/benchmark_results.csv"


def main():
    # Find all .prot files recursively under monitor/tests/
    search_pattern = os.path.join(TEST_ROOT, "**", "*.prot")
    prot_files = sorted(glob.glob(search_pattern, recursive=True))

    if not prot_files:
        print(f"No .prot files found under {TEST_ROOT}/")
        return

    rows = []

    for pf in tqdm(prot_files, desc="Benchmarking", unit="file"):
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
            # Run Turnt with `--print` to run the monitor executable directly
            # without Turnt's comparison overhead
            f"turnt --print --env monitor-bench {pf}",
        ]

        # Suppress Turnt's output to avoid measurement overhead
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
        prof_file = pf.replace(".prot", ".prof")
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

        base = os.path.basename(pf)
        if base.endswith(".prot"):
            base = base[:-5]  # strip .prot

        rows.append(
            [
                pf,
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


if __name__ == "__main__":
    main()
