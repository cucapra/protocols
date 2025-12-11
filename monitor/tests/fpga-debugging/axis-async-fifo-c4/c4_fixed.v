// Taken from https://github.com/ngernest/rtl-repair/blob/asplos24/benchmarks/fpga-debugging/axis-async-fifo-c4/axis_async_fifo.v

/*

Copyright (c) 2014 Alex Forencich

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

*/

// Language: Verilog 2001

`timescale 1ns / 1ps

/*
 * AXI4-Stream asynchronous FIFO
 */
module axis_async_fifo #
(
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 8
)
(
    /*
     * Common asynchronous reset
     */
    input  wire                   async_rst,

    /*
     * AXI input
     */
    input  wire                   input_clk,
    input  wire [DATA_WIDTH-1:0]  input_axis_tdata,
    input  wire                   input_axis_tvalid,
    output wire                   input_axis_tready,
    input  wire                   input_axis_tlast,
    input  wire                   input_axis_tuser,
    
    /*
     * AXI output
     */
    input  wire                   output_clk,
    output wire [DATA_WIDTH-1:0]  output_axis_tdata,
    output wire                   output_axis_tvalid,
    input  wire                   output_axis_tready,
    output wire                   output_axis_tlast,
    output wire                   output_axis_tuser
);

reg [ADDR_WIDTH:0] wr_ptr = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_next;
reg [ADDR_WIDTH:0] wr_ptr_gray = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_next;
reg [ADDR_WIDTH:0] rd_ptr_gray = {ADDR_WIDTH+1{1'b0}};

reg [ADDR_WIDTH:0] wr_ptr_gray_sync1 = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_gray_sync2 = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_gray_sync1 = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_gray_sync2 = {ADDR_WIDTH+1{1'b0}};

reg input_rst_sync1 = 1;
reg input_rst_sync2 = 1;
reg input_rst_sync3 = 1;
reg output_rst_sync1 = 1;
reg output_rst_sync2 = 1;
reg output_rst_sync3 = 1;

reg [DATA_WIDTH+2-1:0] data_out_reg = {1'b0, 1'b0, {DATA_WIDTH{1'b0}}};

//(* RAM_STYLE="BLOCK" *)
reg [DATA_WIDTH+2-1:0] mem[(2**ADDR_WIDTH)-1:0];

reg output_axis_tvalid_reg = 1'b0;

wire [DATA_WIDTH+2-1:0] data_in = {input_axis_tlast, input_axis_tuser, input_axis_tdata};

// full when first TWO MSBs do NOT match, but rest matches
// (gray code equivalent of first MSB different but rest same)
wire full = ((wr_ptr_gray[ADDR_WIDTH] != rd_ptr_gray_sync2[ADDR_WIDTH]) &&
             (wr_ptr_gray[ADDR_WIDTH-1] != rd_ptr_gray_sync2[ADDR_WIDTH-1]) &&
             (wr_ptr_gray[ADDR_WIDTH-2:0] == rd_ptr_gray_sync2[ADDR_WIDTH-2:0]));
// empty when pointers match exactly
wire empty = rd_ptr_gray == wr_ptr_gray_sync2;

wire write = input_axis_tvalid & ~full;
wire read = (output_axis_tready | ~output_axis_tvalid_reg) & ~empty;

assign {output_axis_tlast, output_axis_tuser, output_axis_tdata} = data_out_reg;

// Fix: Reset-Data Synchronization
// `input_axis_tready` is now dependent ~input_rst_sync3, preventing data acceptance during reset
//
// The reset synchronization code in lines 139-149 creates a 3-cycle delay:
//   Cycle 0: async_rst deasserts, but input_rst_sync1/2/3 are all still 1
//   Cycle 1: input_rst_sync1 becomes 0, but input_rst_sync2/3 are still 1
//   Cycle 2: input_rst_sync2 becomes 0, but input_rst_sync3 is still 1
//   Cycle 3: input_rst_sync3 becomes 0 (reset complete)
//
// The fix in the line below ensures that data is only accepted after the reset completes:
// ```verilog
// input_axis_tready = ~full & ~input_rst_sync3
// ```
// - During cycles 0-2: input_rst_sync3 = 1, so tready = 0 (blocks all writes)
// - Starting cycle 3: input_rst_sync3 = 0, so tready depends only on ~full
// - `write = input_axis_tvalid & ~full` (line 102) can only be 1 after reset sync completes
// - The write pointer `wr_ptr_next` is guaranteed to be properly initialized before any writes
//
// Correct behavior: No data acceptance until FIFO is fully initialized
//
// Inferred transaction-level trace by the monitor (`c4_fixed.out`):
//   Time 0-25ns:    reset() - async_rst is 1
//   Time 25-50ns:   idle() - input_rst_sync3 still 1, tready = 0 (this is OK)
//   Time 50-75ns:   push(1) - First write after reset sync completes
//                   Data pushed to FIFO but not yet readable on the output side
//   Time 100-150ns: push_and_pop(3,3) - Normal operation begins
//                   Both push and pop can now complete (output side also synced)
//
// By making `tready` dependent on `~input_rst_sync3`, the FIFO correctly 
// rejects writes during the reset synchronization period, as desired.
assign input_axis_tready = ~full  & ~input_rst_sync3;
assign output_axis_tvalid = output_axis_tvalid_reg;

// reset synchronization
always @(posedge input_clk) begin
    if (async_rst) begin
        input_rst_sync1 <= 1;
        input_rst_sync2 <= 1;
        input_rst_sync3 <= 1;
    end else begin
        input_rst_sync1 <= 0;
        input_rst_sync2 <= input_rst_sync1 | output_rst_sync1;
        input_rst_sync3 <= input_rst_sync2;
    end
end

always @(posedge output_clk) begin
    if (async_rst) begin
        output_rst_sync1 <= 1;
        output_rst_sync2 <= 1;
        output_rst_sync3 <= 1;
    end else begin
        output_rst_sync1 <= 0;
        output_rst_sync2 <= output_rst_sync1;
        output_rst_sync3 <= output_rst_sync2;
    end
end

// write
assign wr_ptr_next = wr_ptr + 1;
always @(posedge input_clk) begin
    if (input_rst_sync3) begin
        wr_ptr <= 0;
        wr_ptr_gray <= 0;
    end else if (write) begin
        mem[wr_ptr[ADDR_WIDTH-1:0]] <= data_in;
        wr_ptr <= wr_ptr_next;
        wr_ptr_gray <= wr_ptr_next ^ (wr_ptr_next >> 1);
    end
end

// pointer synchronization
always @(posedge input_clk) begin
    if (input_rst_sync3) begin
        rd_ptr_gray_sync1 <= 0;
        rd_ptr_gray_sync2 <= 0;
    end else begin
        rd_ptr_gray_sync1 <= rd_ptr_gray;
        rd_ptr_gray_sync2 <= rd_ptr_gray_sync1;
    end
end

// read
assign rd_ptr_next = rd_ptr + 1;
always @(posedge output_clk) begin
    if (output_rst_sync3) begin
        rd_ptr <= 0;
        rd_ptr_gray <= 0;
    end else if (read) begin
        data_out_reg <= mem[rd_ptr[ADDR_WIDTH-1:0]];
        rd_ptr <= rd_ptr_next;
        rd_ptr_gray <= rd_ptr_next ^ (rd_ptr_next >> 1);
    end
end

// pointer synchronization
always @(posedge output_clk) begin
    if (output_rst_sync3) begin
        wr_ptr_gray_sync1 <= 0;
        wr_ptr_gray_sync2 <= 0;
    end else begin
        wr_ptr_gray_sync1 <= wr_ptr_gray;
        wr_ptr_gray_sync2 <= wr_ptr_gray_sync1;
    end
end

// source ready output
always @(posedge output_clk) begin
    if (output_rst_sync3) begin
        output_axis_tvalid_reg <= 1'b0;
    end else if (output_axis_tready | ~output_axis_tvalid_reg) begin
        output_axis_tvalid_reg <= ~empty;
    end else begin
        output_axis_tvalid_reg <= output_axis_tvalid_reg;
    end
end

endmodule
