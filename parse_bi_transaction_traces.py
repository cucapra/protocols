#!/usr/bin/env python3
"""Analyzes the output of the BI and classifies tranasctions 
as idle, reset, or non-trivial (i.e. not idle and not reset), 
computing the no. of cycles taken for each type of transactions.

Note:
- We assume there is only one trace in the BI output
- We assume that the BI output was produced using `--include-idle` and `--show-waveform-time`
  (i.e. timing information in ns and idle transactions are included in the BI output)
"""

import argparse
import re
import sys

# Regex matching a transaction's name, its start time and its end time in the BI's output
TRANSACTION_RE = re.compile(
    r"(?P<transaction>.*?);  // \[time: (?P<start>\d+)ns -> (?P<end>\d+)ns\]"
)

# Names of idle transactions (this is for `wishbone.prot`)
IDLE_TRANSACTIONS = ("idle_no_cycle", "idle_continue_cycle")


def classify_transaction(transaction):
    """Determines if a transaction is reset, idle or a non-trivial transction (e.g. read/write) based on its name"""
    if transaction.startswith("reset"):
        return "reset"
    elif any(transaction.startswith(tx) for tx in IDLE_TRANSACTIONS):
        return "idle"
    else:
        return "non_trivial"


def parse_bi_output(path):
    """Parses the BI output, extracting (transaction_name, start_ns, end_ns) for each transaction in the transaction trace"""
    lines = []
    with open(path, "r", errors="replace") as f:
        for line in f:
            regex_match = TRANSACTION_RE.match(line.strip())
            if not regex_match:
                continue
            lines.append(
                (
                    regex_match.group("transaction").strip(),
                    int(regex_match.group("start")),
                    int(regex_match.group("end")),
                )
            )
    return lines


def analyze_bi_output(parsed_bi_output, clock_period):
    """Examines the parsed BI output and extracts the tranasction name / type, the start/end time and the no. of cycles taken for the transaction"""
    rows = []
    for transaction, start_ns, end_ns in parsed_bi_output:
        category = classify_transaction(transaction)
        rows.append(
            {
                "transaction_type": category,
                "transaction": transaction,
                "start_ns": start_ns,
                "end_ns": end_ns,
                "cycles": (end_ns - start_ns) / clock_period,
            }
        )
    return rows


def summarize_bi_output(data_rows):
    """Computes the total no. of cycles & no. of transactions for each transaction type (idle, reset, non-trivial),
    based on the provided data_rows argument"""
    summary = {}
    for transaction_type in ("non_trivial", "idle", "reset"):
        num_cycles = [
            row["cycles"]
            for row in data_rows
            if row["transaction_type"] == transaction_type
        ]
        summary[f"No. of {transaction_type} transactions"] = len(num_cycles)
        summary[f"Total no. of {transaction_type} cycles"] = (
            sum(num_cycles) if num_cycles != [] else 0.0
        )
    return summary


def main():
    arg_parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    arg_parser.add_argument(
        "traces",
        nargs="+",
        help="bi output transaction traces, created with --include-idle and --show-waveform-time",
    )
    arg_parser.add_argument(
        "--ns-per-cycle",
        type=float,
        required=True,
        help="clock period in the waveform (no. of ns per clcok cycle)",
    )
    args = arg_parser.parse_args()

    all_summaries = {}
    for bi_output_filepath in args.traces:
        lines = parse_bi_output(bi_output_filepath)
        if not lines:
            print(
                f"Error: Missing '// [time: ...]' lines in BI output, rerun using --show-waveform-time and --include-idle",
                file=sys.stderr,
            )
            exit(1)
        rows = analyze_bi_output(lines, args.ns_per_cycle)
        all_summaries[bi_output_filepath] = summarize_bi_output(rows)

    for bi_output_filepath, summary_stats in all_summaries.items():
        print(f"Statistics for BI output (from {bi_output_filepath}):")
        for k, v in summary_stats.items():
            print(f"\t{k}: {v:.2f}" if isinstance(v, float) else f"\t{k}: {v}")


if __name__ == "__main__":
    main()
