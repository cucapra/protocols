#!/usr/bin/env bash
set -uo pipefail

OUTDIR="${1:-./bi_bench_output}"
mkdir -p "$OUTDIR"

names=(
  "reader_data"
  "reader_control"
  "writer_control"
  "ethmac"
)

commands=(
  "./target/release/bi -p examples/wishbone/wishbone.prot -p examples/wishbone/wb_stream.prot --wave ../protocols-evaluation/wishbone/wb_streamer/wb_stream_reader_tb.fst --instances wb_stream_reader_tb.dut:WishboneData"
  "./target/release/bi -p examples/wishbone/wishbone.prot -p examples/wishbone/wb_stream.prot --wave ../protocols-evaluation/wishbone/wb_streamer/wb_stream_reader_tb.fst --instances wb_stream_reader_tb.dut:WishboneControl --force-x-to-zero"
  "./target/release/bi -p examples/wishbone/wishbone.prot -p examples/wishbone/wb_stream.prot --wave ../protocols-evaluation/wishbone/wb_streamer/wb_stream_writer_tb.fst --instances wb_stream_writer_tb.dut:WishboneControl --force-x-to-zero"
  "./target/release/bi -p examples/wishbone/wishbone.prot -p examples/wishbone/ethmac.prot --instances tb_ethernet.wb_master.wbm_low_level:Tb_ethernetWb_masterWbm_low_level --display-hex --show-waveform-time --wave ../protocols-evaluation/wishbone/ethmac/ethmac.fst --include-idle"
)

echo "Capturing single-run output for inspection into $OUTDIR ..."
for i in "${!names[@]}"; do
  name="${names[$i]}"
  cmd="${commands[$i]}"
  echo " -> $name"
  if ! bash -c "$cmd" > "$OUTDIR/${name}.log" 2> "$OUTDIR/${name}.err.log"; then
    echo "    FAILED (see $OUTDIR/${name}.err.log)"
  fi
done

echo "Running hyperfine for timing ..."
hyperfine_args=(--warmup 3 --min-runs 10 --ignore-failure --export-json "$OUTDIR/timings.json" --export-markdown "$OUTDIR/timings.md")
for name in "${names[@]}"; do
  hyperfine_args+=(-n "$name")
done
for cmd in "${commands[@]}"; do
  hyperfine_args+=("$cmd")
done

hyperfine "${hyperfine_args[@]}"
