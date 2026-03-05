#!/usr/bin/env python3
"""
Check for performance regressions in the monitor
by comparing current benchmark results with a baseline (the existing CSV
in the `benchmark_results` sub-directory).
"""

import csv
import sys
import os

BASELINE_CSV = "benchmark_results/baseline_results.csv"
CURRENT_CSV = "benchmark_results/benchmark_results.csv"
REGRESSION_THRESHOLD = 0.10  # 10% slower is considered a regression


def load_results(csv_path):
    """Load benchmark results from CSV into a dict keyed by test_name."""
    results = {}
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            test_name = row["test_name"]
            results[test_name] = {
                "mean_per_step": float(row["mean_per_step"]),
                "stddev_per_step": float(row["stddev_per_step"]),
                "min_per_step": float(row["min_per_step"]),
                "max_per_step": float(row["max_per_step"]),
                "steps_per_sec": float(row["steps_per_sec"]),
            }
    return results


def main():
    if not os.path.exists(BASELINE_CSV):
        print(f"No baseline found at {BASELINE_CSV}")
        print("Creating baseline from current results...")
        # Copy current results as baseline
        os.makedirs(os.path.dirname(BASELINE_CSV), exist_ok=True)
        with open(CURRENT_CSV) as src, open(BASELINE_CSV, "w") as dst:
            dst.write(src.read())
        print(f"Baseline saved to {BASELINE_CSV}")
        return 0

    baseline = load_results(BASELINE_CSV)
    current = load_results(CURRENT_CSV)

    regressions = []
    improvements = []

    print("\n=== Performance Comparison ===\n")

    for test_name in sorted(current.keys()):
        if test_name not in baseline:
            steps_per_sec = current[test_name]["steps_per_sec"]
            print(f"NEW: {test_name}: {steps_per_sec:.2f} steps/sec")
            continue

        # Read pre-computed throughput (steps per second)
        baseline_throughput = baseline[test_name]["steps_per_sec"]
        current_throughput = current[test_name]["steps_per_sec"]

        # Calculate percentage change (positive = improvement, negative = regression)
        pct_change = (
            (current_throughput - baseline_throughput) / baseline_throughput
        ) * 100

        status = "="
        if pct_change < -REGRESSION_THRESHOLD * 100:
            # Throughput decreased by more than threshold = regression
            status = "REGRESSION"
            regressions.append(
                (test_name, baseline_throughput, current_throughput, pct_change)
            )
        elif pct_change > REGRESSION_THRESHOLD * 100:
            # Throughput increased by more than threshold = improvement
            status = "IMPROVEMENT"
            improvements.append(
                (test_name, baseline_throughput, current_throughput, pct_change)
            )

        print(
            f"{status:12} {test_name:30} {baseline_throughput:7.2f} -> {current_throughput:7.2f} steps/sec ({pct_change:+6.2f}%)"
        )

    print()

    if regressions:
        print(f"\nFound {len(regressions)} performance regression(s):")
        for (
            test_name,
            baseline_throughput,
            current_throughput,
            pct_change,
        ) in regressions:
            print(
                f"  - {test_name}: {baseline_throughput:.2f} -> {current_throughput:.2f} steps/sec ({pct_change:+.2f}%)"
            )
        return 1

    if improvements:
        print(f"\nFound {len(improvements)} performance improvement(s):")
        for (
            test_name,
            baseline_throughput,
            current_throughput,
            pct_change,
        ) in improvements:
            print(
                f"  - {test_name}: {baseline_throughput:.2f} -> {current_throughput:.2f} steps/sec ({pct_change:+.2f}%)"
            )

    print("\nNo performance regressions detected!")
    return 0


if __name__ == "__main__":
    sys.exit(main())
