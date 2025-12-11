#!/usr/bin/env python3
"""
Plots the data in `INPUT_CSV` as a scatter plot, saving it in `OUTPUT_PNG`
"""

import csv
import math
import matplotlib.pyplot as plt

INPUT_CSV = "benchmark_results/benchmark_results.csv"
OUTPUT_PNG = "benchmark_results/benchmark_plot.png"

def main():
    names = []
    means_ms = []

    with open(INPUT_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            names.append(row["test_name"])
            # Convert seconds to milliseconds
            means_ms.append(float(row["mean"]) * 1000.0)

    # Determine min/max time, round them to nearest 10 ms boundaries
    min_ms = min(means_ms)
    max_ms = max(means_ms)
    ymin = math.floor(min_ms / 10.0) * 10.0
    ymax = math.ceil(max_ms / 10.0) * 10.0

    # Create ticks every 10 ms
    yticks = list(range(int(ymin), int(ymax) + 1, 10))

    plt.figure(figsize=(12, 6))
    plt.scatter(names, means_ms)

    plt.title("Mean monitor execution time on benchmarks (lower is better)")
    plt.xlabel("Test File")
    plt.ylabel("Mean wall-clock time over 10 executions (ms)")
    plt.xticks(rotation=45, ha="right")

    # Apply explicit 10 ms ticks
    plt.yticks(yticks)

    plt.grid(zorder=1, linestyle="--", alpha=0.6)
    plt.tight_layout()
    plt.savefig(OUTPUT_PNG)

    print(f"Saved plot to {OUTPUT_PNG}")
    
    plt.close()

if __name__ == "__main__":
    main()