// This file is used to rename ports so that the interpreter can drive the design.
// The signals in waveforms used by the BI (obtained directly from the Brave New World artifact) 
// uses names such as `axis_reg_inst.s_axis_tdata`, but the Verilog DUT (in `c4_buggy.v` / `c4_fixed.v`)
// uses names such as `input_axis_tdata`, so this file renames them.

`timescale 1ns / 1ps

module c4_dut (
    input  wire       clk,
    input  wire       rst,

    // AXI-Stream input (write / push) side
    input  wire [7:0] s_axis_tdata,
    input  wire       s_axis_tvalid,
    output wire       s_axis_tready,

    // AXI-Stream output (read / pop) side
    input  wire       m_axis_tready,
    output wire       m_axis_tvalid,
    output wire [7:0] m_axis_tdata
);

axis_async_fifo #(
    .ADDR_WIDTH(5),
    .DATA_WIDTH(8)
)
fifo (
    .async_rst(rst),

    // AXI input
    .input_clk(clk),
    .input_axis_tdata(s_axis_tdata),
    .input_axis_tvalid(s_axis_tvalid),
    .input_axis_tready(s_axis_tready),
    .input_axis_tlast(1'b0),
    .input_axis_tuser(1'b0),

    // AXI output
    .output_clk(clk),
    .output_axis_tdata(m_axis_tdata),
    .output_axis_tvalid(m_axis_tvalid),
    .output_axis_tready(m_axis_tready),
    .output_axis_tlast(),
    .output_axis_tuser()
);

endmodule
