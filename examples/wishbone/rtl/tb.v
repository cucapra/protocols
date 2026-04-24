// source: https://github.com/antmicro/wishbone-interconnect-burst-mode-benchmark
// modifications:
// - wishbone pin names
// - tied fifo and sram I/O to zero
// - remove test_name input

`timescale 100ps / 1ps

module tb(
  input clk,
  input RST,
  input [31:0] ADR,
  input [31:0] DAT_O,
  output [31:0] DAT_I,
  input CYC,
  input STB,
  output ACK,
  input WE,
  input [3:0] SEL,
  output ERR,
  input [2:0] CTI,
  input wire [1:0] BTE
);


wire [31:0] io_fifo_dat_rx = 0;
wire [31:0] io_fifo_dat_tx;
wire io_fifo_stb_rx = 0;
wire io_fifo_stb_tx;
wire io_fifo_wait_rx;
wire io_fifo_wait_tx;
wire [5:0] io_sram_adr = 0;
wire [31:0] io_sram_datrd;
wire [31:0] io_sram_datwr = 0;
wire io_sram_we = 0;
wire n_reset;
assign n_reset = ~RST;

  dut dut(
    .clk(clk),
    .reset(n_reset),
    .wishbone_adr(ADR[29:0]),
    .wishbone_dat_r(DAT_I),
    .wishbone_dat_w(DAT_O),
    .wishbone_cyc(CYC),
    .wishbone_stb(STB),
    .wishbone_ack(ACK),
    .wishbone_we(WE),
    .wishbone_sel(SEL),
    .wishbone_cti(CTI),
    .wishbone_bte(BTE),
    .wishbone_err(ERR),
    .fifo_dat_rx(io_fifo_dat_rx),
    .fifo_dat_tx(io_fifo_dat_tx),
    .fifo_stb_rx(io_fifo_stb_rx),
    .fifo_stb_tx(io_fifo_stb_tx),
    .fifo_wait_rx(io_fifo_wait_rx),
    .fifo_wait_tx(io_fifo_wait_tx),
    .sram_adr(io_sram_adr),
    .sram_dat_r(io_sram_datrd),
    .sram_dat_w(io_sram_datwr),
    .sram_we(io_sram_we)
  );

  // Dump waves
  //initial begin
    //$dumpfile("dump.vcd");
    //$dumpvars(0, tb);
  //end

endmodule
