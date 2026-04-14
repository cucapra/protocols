# wb_streamer

Traces from the wb_streamer core from FuseSoc. We used version `1.1`.

Fork used: https://github.com/ngernest/wb_streamer

## Generating waveforms

We ran the following in the fork above:

```bash
uv run fusesoc library add fusesoc-cores https://github.com/fusesoc/fusesoc-cores

# writer (stream -> memory)
uv run fusesoc run --flag stream_bfm --tool=icarus --target=sim wb_streamer

# reader (memory -> stream)
uv run fusesoc run --flag stream_bfm --tool=icarus --target=sim_reader wb_streamer
```

We then add waveform dumping to the generated testbench right before `@(negedge rst)`, similar to the 
waveforms in the `wb_intercon` folder in this repo:

```verilog
$dumpfile("wb_stream_writer_tb.fst"); $dumpvars(0);
```
