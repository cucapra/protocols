# Note: before running this script, first run 
# `cargo build --release --package protocols-monitor` 

import csv
import json
import subprocess
import glob
import os

TEST_ROOT = "monitor/tests"
OUTPUT_CSV = "benchmark_results.csv"

def main():
    # Find all .prot files recursively under monitor/tests/
    search_pattern = os.path.join(TEST_ROOT, "**", "*.prot")
    prot_files = sorted(glob.glob(search_pattern, recursive=True))

    if not prot_files:
        print(f"No .prot files found under {TEST_ROOT}/")
        return

    print(f"Found {len(prot_files)} .prot files.\n")

    rows = []

    for pf in prot_files:
        print(f"Benchmarking {pf} ...")

        cmd = [
            "hyperfine",
            "--shell=none",
            "--export-json", "tmp_hyperfine.json",
            "--warmup", "3",
            f"turnt --env monitor {pf}",
        ]

        subprocess.run(cmd, check=True)

        # Load hyperfine JSON
        with open("tmp_hyperfine.json") as f:
            data = json.load(f)

        result = data["results"][0]
        mean_time = result["mean"]
        stddev = result["stddev"]
        min_time = result["min"]
        max_time = result["max"]

        base = os.path.basename(pf)
        if base.endswith(".prot"):
            base = base[:-5]  # strip .prot

        rows.append([pf, base, mean_time, stddev, min_time, max_time])

    # ---- Write CSV ----
    with open(OUTPUT_CSV, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["file_path", "test_name", "mean", "stddev", "min", "max"])
        writer.writerows(rows)

    print(f"\nWrote results to {OUTPUT_CSV}")


if __name__ == "__main__":
    main()

