import csv
import matplotlib.pyplot as plt

INPUT_CSV = "benchmark_results.csv"

def main():
    names = []
    means = []

    with open(INPUT_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            names.append(row["test_name"])
            means.append(float(row["mean"]))

    plt.figure(figsize=(12, 6))
    plt.scatter(names, means)

    plt.title("Monitor Execution Time on Benchmarks")
    plt.xlabel("Test File")
    plt.ylabel("Mean Wall-clock Time (seconds)")
    plt.xticks(rotation=75, ha="right")
    plt.grid(True, axis="y")
    plt.tight_layout()
    plt.savefig("benchmark_plot.png")

    print("Saved plot to benchmark_plot.png")

if __name__ == "__main__":
    main()