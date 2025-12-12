#!/usr/bin/env python3
"""
Plots the data in `INPUT_CSV` as a scatter plot, saving it in `OUTPUT_PNG`
"""

import csv
import math
import matplotlib
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

    plt.figure(figsize=(12, 8))
    plt.scatter(names, steps_per_sec)

    plt.title("Monitor throughput on benchmarks (higher is better)")
    plt.xlabel("Test File")
    plt.ylabel("`Step`s (clock cycles) per second")
    plt.xticks(rotation=45, ha="right")

    plt.grid(zorder=1, linestyle="--", alpha=0.6)
    plt.tight_layout()
    plt.savefig(OUTPUT_PNG)

    print(f"Saved plot to {OUTPUT_PNG}")
    
    plt.close()

if __name__ == "__main__":
    main()