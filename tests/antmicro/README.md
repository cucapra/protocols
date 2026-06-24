# Antmicro Wishbone Burst Mode Benchmark

This folder contains the monitor's inferred transaction traces for waveforms obtained from a benchmark suite for [Wishbone's burst mode](https://github.com/antmicro/wishbone-interconnect-burst-mode-benchmark). 

Sources:
- blog post: https://antmicro.com/blog/2022/05/faster-soc-interconnects-with-test-driven-fpga-development-and-cocotb
- original repo: https://github.com/antmicro/wishbone-interconnect-burst-mode-benchmark
- fork with ci changes to get all FSTs: https://github.com/ekiwi/wishbone-interconnect-burst-mode-benchmark

There are 4 sub-folders, corresponding to the different combinations
of workloads and Wishbone implementations in the benchmark:
- `fifo_classic`: Wishbone FIFO in classic (non-burst) mode
- `fifo_constant`: Wishbone FIFO in burst mode, where the address is kept constant
- `sram_classic`: Wishbone SRAM in classic mode
- `sram_incrementing`: Wishbone SRAM in burst mode with incrementing addresses

Naming conventions:
- For `fifo_classic` & `fifo_constant`, the `.fst` files 
are all named `test_fifo_{cycle_type}_{n}.fst`, where `cycle_type` is either 
`classic` or `constant`, and `n` is 1-8 (no. of repeated reads & writes to execute). Likewise for the `.prot` and `.out / .err` output files.
- For `sram_classic`: naming convention is `test_sram_classic_{burst_len}_{offset}.fst`, where:
  - `burst_len` is 1, 2, 4, 8, 16 (burst length)
  - `offset` is 0, 4, 8, 12 (the offset that the starting address is subject to)
- For `sram_incrementing`, naming convention is `test_sram_incrementing_{burst_len}_{offset}_{iteration}.fst`, where:
  - `burst_len` is 1, 2, 4, 8, 16 (burst length)
  - `offset` is 0, 4, 8, 12 (the offset that the starting address is subject to)
  - `iteration` is 0, 1, 2, 3 (4 different iterations for each `burst_len * offset` combination, where each iteration uses a different random seed to produce the data values)

