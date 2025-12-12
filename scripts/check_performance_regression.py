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
            print(f"NEW: {test_name}: {current[test_name]['mean_per_step']*1000:.2f}ms/step")
            continue

        baseline_mean = baseline[test_name]["mean_per_step"]
        current_mean = current[test_name]["mean_per_step"]

        # Calculate percentage change
        pct_change = ((current_mean - baseline_mean) / baseline_mean) * 100

        # Convert to milliseconds per step for display
        baseline_ms = baseline_mean * 1000
        current_ms = current_mean * 1000

        status = "="
        if pct_change > REGRESSION_THRESHOLD * 100:
            status = "REGRESSION"
            regressions.append((test_name, baseline_ms, current_ms, pct_change))
        elif pct_change < -REGRESSION_THRESHOLD * 100:
            status = "IMPROVEMENT"
            improvements.append((test_name, baseline_ms, current_ms, pct_change))

        print(f"{status:12} {test_name:30} {baseline_ms:7.2f}ms/step -> {current_ms:7.2f}ms/step ({pct_change:+6.2f}%)")

    print()

    if regressions:
        print(f"\nFound {len(regressions)} performance regression(s):")
        for test_name, baseline_ms, current_ms, pct_change in regressions:
            print(f"  - {test_name}: {baseline_ms:.2f}ms/step -> {current_ms:.2f}ms/step ({pct_change:+.2f}%)")
        return 1

    if improvements:
        print(f"\nFound {len(improvements)} performance improvement(s):")
        for test_name, baseline_ms, current_ms, pct_change in improvements:
            print(f"  - {test_name}: {baseline_ms:.2f}ms/step -> {current_ms:.2f}ms/step ({pct_change:+.2f}%)")

    print("\nNo performance regressions detected!")
    return 0

if __name__ == "__main__":
    sys.exit(main())
