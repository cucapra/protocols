# `wb_intercon`

Traces from the wishbone interconnect core from FuseSoc.
We used version `1.4.1`.

The simulation was created with:
```
fusesoc run  --tool=icarus --target=sim wb_intercon
```

We then manually modified the toplevel in order to run testbenches one by one
and in order to enable waveform dumping.
The toplevel was found at: `build/wb_intercon_1.4.1/sim-icarus/src/wb_intercon_1.4.1/bench/wb_intercon_tb.v`

The generated `Makefile` does not correct track dependencies and thus, the simulation
must be deleted after making a change to a Verilog file.

Thus we would run:

```
rm wb_intercon_1.4.1
make run
```

## `wb_mux.fst`

We modified `wb_intercon_tb.v` like this:

```
      $dumpfile("wb_mux.fst"); $dumpvars (0);
      wb_mux_tb.run;
      vtg.ok("wb_mux: All tests passed!");
```


## `wb_arb.fst`

```
      wb_mux_tb.run;
      vtg.ok("wb_mux: All tests passed!");
      
      $dumpfile("wb_arb.fst"); $dumpvars (0);
      wb_arb_tb.run;
      vtg.ok("wb_arbiter: All tests passed!");
```


## `wb_cdc.fst`

```
      wb_mux_tb.run;
      vtg.ok("wb_mux: All tests passed!");
      
      wb_arb_tb.run;
      vtg.ok("wb_arbiter: All tests passed!");

      $dumpfile("wb_cdc.fst"); $dumpvars (0);
      wb_cdc_tb.run;
      vtg.ok("wb_cdc: All tests passed!");
```


**Note**: Just removing the tests that we do not want to record did not work.
The system would just hang.
