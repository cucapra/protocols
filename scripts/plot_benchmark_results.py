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
    steps_per_sec = []

    with open(INPUT_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            names.append(row["test_name"])
            # Read pre-computed throughput (steps per second)
            steps_per_sec.append(float(row["steps_per_sec"]))

    # Determine min/max values on the y-axis, round them to nearest multiple of 10
    min_steps_per_sec = min(steps_per_sec)
    max_steps_per_sec = max(steps_per_sec)
    ymin = math.floor(min_steps_per_sec / 10.0) * 10.0
    ymax = math.ceil(max_steps_per_sec / 10.0) * 10.0

    # Create ticks for every 200 units on the y-axis
    yticks = list(range(int(ymin), int(ymax) + 1, 200))

    plt.figure(figsize=(12, 8))
    plt.scatter(names, steps_per_sec)

    plt.title("Monitor throughput on benchmarks (higher is better)")
    plt.xlabel("Test File")
    plt.ylabel("Mean no. of Steps (clock cycles) per second")
    plt.xticks(rotation=45, ha="right")
    plt.yticks(yticks)

    plt.grid(zorder=1, linestyle="--", alpha=0.6)
    plt.tight_layout()
    plt.savefig(OUTPUT_PNG)

    print(f"Saved plot to {OUTPUT_PNG}")

    plt.close()


if __name__ == "__main__":
    main()
