// From https://github.com/ngernest/rtl-repair/blob/asplos24/benchmarks/fpga-debugging/axis-fifo-d4/axis_fifo_bug_d4.v

/*

Copyright (c) 2013-2018 Alex Forencich

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

/*verilator lint_off SELRANGE*/

/*
 * AXI4-Stream FIFO
 */
module axis_fifo #
(
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter LAST_ENABLE = 1,
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1,
    parameter FRAME_FIFO = 0,
    parameter USER_BAD_FRAME_VALUE = 1'b1,
    parameter USER_BAD_FRAME_MASK = 1'b1,
    parameter DROP_BAD_FRAME = 0,
    parameter DROP_WHEN_FULL = 0
)
(
    input  wire                   clk,
    input  wire                   rst,

    /*
     * AXI input
     */
    input  wire [DATA_WIDTH-1:0]  s_axis_tdata,
    input  wire [KEEP_WIDTH-1:0]  s_axis_tkeep,
    input  wire                   s_axis_tvalid,
    output wire                   s_axis_tready,
    input  wire                   s_axis_tlast,
    input  wire [ID_WIDTH-1:0]    s_axis_tid,
    input  wire [DEST_WIDTH-1:0]  s_axis_tdest,
    input  wire [USER_WIDTH-1:0]  s_axis_tuser,

    /*
     * AXI output
     */
    output wire [DATA_WIDTH-1:0]  m_axis_tdata,
    output wire [KEEP_WIDTH-1:0]  m_axis_tkeep,
    output wire                   m_axis_tvalid,
    input  wire                   m_axis_tready,
    output wire                   m_axis_tlast,
    output wire [ID_WIDTH-1:0]    m_axis_tid,
    output wire [DEST_WIDTH-1:0]  m_axis_tdest,
    output wire [USER_WIDTH-1:0]  m_axis_tuser,

    /*
     * Status
     */
    output wire                   status_overflow,
    output wire                   status_bad_frame,
    output wire                   status_good_frame
);


localparam KEEP_OFFSET = DATA_WIDTH;
localparam LAST_OFFSET = KEEP_OFFSET + (KEEP_ENABLE ? KEEP_WIDTH : 0);
localparam ID_OFFSET   = LAST_OFFSET + (LAST_ENABLE ? 1          : 0);
localparam DEST_OFFSET = ID_OFFSET   + (ID_ENABLE   ? ID_WIDTH   : 0);
localparam USER_OFFSET = DEST_OFFSET + (DEST_ENABLE ? DEST_WIDTH : 0);
localparam WIDTH       = USER_OFFSET + (USER_ENABLE ? USER_WIDTH : 0);

// Ring Buffer Pointers - Use (ADDR_WIDTH+1) bits for full/empty detection
// - ADDR_WIDTH bits: Memory address (wraps around 0 to 2^ADDR_WIDTH-1)
// - Extra MSB bit: Wrap-around tracking to distinguish full from empty
// Example: ADDR_WIDTH=2 means 4 memory locations, but pointers count 0-7
//   When wr_ptr=4 and rd_ptr=0: MSB differs (1 vs 0), lower bits match (00 vs 00) → FULL
//   When wr_ptr=0 and rd_ptr=0: All bits match → EMPTY
reg [ADDR_WIDTH:0] wr_ptr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_next;
reg [ADDR_WIDTH:0] wr_ptr_cur_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_cur_next;
reg [ADDR_WIDTH:0] wr_addr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_next;
reg [ADDR_WIDTH:0] rd_addr_reg = {ADDR_WIDTH+1{1'b0}};

// Ring Buffer Memory - Capacity = 2^ADDR_WIDTH entries
// Example: ADDR_WIDTH=2 → 4 entries (addresses 0,1,2,3 wrap around)
reg [WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0];
reg [WIDTH-1:0] mem_read_data_reg;
reg mem_read_data_valid_reg = 1'b0;
reg mem_read_data_valid_next;

wire [WIDTH-1:0] s_axis;

reg [WIDTH-1:0] m_axis_reg;
reg m_axis_tvalid_reg = 1'b0;
reg m_axis_tvalid_next;

// BUFFER FULLNESS INDICATORS:
//
// full: Committed write pointer (wr_ptr_reg) has wrapped around to read pointer
//   - Indicates buffer is full based on COMMITTED frames
//   - Only updated when tlast=1 (end of frame)
//   - Problem: Does NOT reflect space used by in-progress multi-beat frame!
wire full = ((wr_ptr_reg[ADDR_WIDTH] != rd_ptr_reg[ADDR_WIDTH]) &&
             (wr_ptr_reg[ADDR_WIDTH-1:0] == rd_ptr_reg[ADDR_WIDTH-1:0]));

// empty: Write and read pointers are equal (no data in buffer)
wire empty = wr_ptr_reg == rd_ptr_reg;

// full_cur: Current write pointer (wr_ptr_cur_reg) has wrapped to read pointer
//   - Indicates ACTUAL buffer fullness including in-progress frame
//   - Updated every cycle as frame is being written
//   - Correctly detects when current frame would overflow the buffer
wire full_cur = ((wr_ptr_reg[ADDR_WIDTH] != wr_ptr_cur_reg[ADDR_WIDTH]) &&
                 (wr_ptr_reg[ADDR_WIDTH-1:0] == wr_ptr_cur_reg[ADDR_WIDTH-1:0]));

// control signals
reg write;
reg read;
reg store_output;

reg drop_frame_reg = 1'b0;
reg drop_frame_next;
reg overflow_reg = 1'b0;
reg overflow_next;
reg bad_frame_reg = 1'b0;
reg bad_frame_next;
reg good_frame_reg = 1'b0;
reg good_frame_next;

// BUG: Uses `full` instead of `full_cur` for ready signal
// This causes buffer overflow because:
// 1. `full` is only updated when frame completes (tlast=1)
// 2. While writing a multi-beat frame, `full` stays 0 even though buffer fills up
// 3. s_axis_tready stays high, accepting more data than buffer can hold
// 4. wr_ptr_cur_reg wraps around and overwrites unread data -> Buffer overflow

// Example: Buffer has 4 slots, contains [A, B, _, _]
//   - wr_ptr_reg=2 (next commit position), rd_ptr_reg=0
//   - full=0 (wr_ptr_reg hasn't wrapped to rd_ptr_reg)
//   - Start writing 4-beat frame [C, D, E, F]:
//     * Write C at index 2: wr_ptr_cur_reg=3, full_cur=0, s_axis_tready=1 (OK)
//     * Write D at index 3: wr_ptr_cur_reg=4, full_cur=0, s_axis_tready=1 (OK)
//     * Write E at index 0: wr_ptr_cur_reg=5, full_cur=1, but s_axis_tready=1! (Bug)
//     * E overwrites A! → Buffer overflow occurs
assign s_axis_tready = (!full || DROP_WHEN_FULL);

generate
    assign s_axis[DATA_WIDTH-1:0] = s_axis_tdata;
    if (KEEP_ENABLE) assign s_axis[KEEP_OFFSET +: KEEP_WIDTH] = s_axis_tkeep;
    if (LAST_ENABLE) assign s_axis[LAST_OFFSET]               = s_axis_tlast;
    if (ID_ENABLE)   assign s_axis[ID_OFFSET   +: ID_WIDTH]   = s_axis_tid;
    if (DEST_ENABLE) assign s_axis[DEST_OFFSET +: DEST_WIDTH] = s_axis_tdest;
    if (USER_ENABLE) assign s_axis[USER_OFFSET +: USER_WIDTH] = s_axis_tuser;
endgenerate

assign m_axis_tvalid = m_axis_tvalid_reg;

assign m_axis_tdata = m_axis_reg[DATA_WIDTH-1:0];
assign m_axis_tkeep = KEEP_ENABLE ? m_axis_reg[KEEP_OFFSET +: KEEP_WIDTH] : {KEEP_WIDTH{1'b1}};
assign m_axis_tlast = LAST_ENABLE ? m_axis_reg[LAST_OFFSET]               : 1'b1;
assign m_axis_tid   = ID_ENABLE   ? m_axis_reg[ID_OFFSET   +: ID_WIDTH]   : {ID_WIDTH{1'b0}};
assign m_axis_tdest = DEST_ENABLE ? m_axis_reg[DEST_OFFSET +: DEST_WIDTH] : {DEST_WIDTH{1'b0}};
assign m_axis_tuser = USER_ENABLE ? m_axis_reg[USER_OFFSET +: USER_WIDTH] : {USER_WIDTH{1'b0}};

assign status_overflow = overflow_reg;
assign status_bad_frame = bad_frame_reg;
assign status_good_frame = good_frame_reg;


// Write logic
always @* begin
    write = 1'b0;

    drop_frame_next = 1'b0;
    overflow_next = 1'b0;
    bad_frame_next = 1'b0;
    good_frame_next = 1'b0;

    wr_ptr_next = wr_ptr_reg;
    wr_ptr_cur_next = wr_ptr_cur_reg;

    if (s_axis_tvalid) begin
        // input data valid
        if (!full || DROP_WHEN_FULL) begin
            // not full, perform write
            if (!FRAME_FIFO) begin
                // PUSH: normal FIFO mode - unconditional write
                write = 1'b1;
                wr_ptr_next = wr_ptr_reg + 1;
            end else if (full || full_cur || drop_frame_reg) begin
                // IDLE: full, packet overflow, or currently dropping frame
                // drop frame
                drop_frame_next = 1'b1;
                if (s_axis_tlast) begin
                    // end of frame, reset write pointer
                    wr_ptr_cur_next = wr_ptr_reg;
                    drop_frame_next = 1'b0;
                    overflow_next = 1'b1;
                end
            end else begin
                // PUSH: frame FIFO mode - write to memory
                write = 1'b1;
                wr_ptr_cur_next = wr_ptr_cur_reg + 1;
                if (s_axis_tlast) begin
                    // end of frame
                    if (DROP_BAD_FRAME && (USER_BAD_FRAME_MASK & s_axis_tuser == USER_BAD_FRAME_VALUE)) begin
                        // bad packet, reset write pointer
                        wr_ptr_cur_next = wr_ptr_reg;
                        bad_frame_next = 1'b1;
                    end else begin
                        // good packet, update write pointer
                        wr_ptr_next = wr_ptr_cur_reg + 1;
                        good_frame_next = 1'b1;
                    end
                end
            end
        end
    end
end

always @(posedge clk) begin
    if (rst) begin
        // RESET: Initialize write-side registers
        wr_ptr_reg <= {ADDR_WIDTH+1{1'b0}};
        wr_ptr_cur_reg <= {ADDR_WIDTH+1{1'b0}};

        drop_frame_reg <= 1'b0;
        overflow_reg <= 1'b0;
        bad_frame_reg <= 1'b0;
        good_frame_reg <= 1'b0;
    end else begin
        // Update write state (PUSH or IDLE)
        wr_ptr_reg <= wr_ptr_next;
        wr_ptr_cur_reg <= wr_ptr_cur_next;

        drop_frame_reg <= drop_frame_next;
        overflow_reg <= overflow_next;
        bad_frame_reg <= bad_frame_next;
        good_frame_reg <= good_frame_next;
    end

    if (FRAME_FIFO) begin
        wr_addr_reg <= wr_ptr_cur_next;
    end else begin
        wr_addr_reg <= wr_ptr_next;
    end

    if (write) begin
        // PUSH: Write data to memory
        // Ring buffer wrap-around: Use only lower ADDR_WIDTH bits as memory index
        // Example: wr_addr_reg=3'b100 (4) → mem[0] (wraps to address 0)
        mem[wr_addr_reg[ADDR_WIDTH-1:0]] <= s_axis;
    end
end

// Read logic
always @* begin
    read = 1'b0;

    rd_ptr_next = rd_ptr_reg;

    mem_read_data_valid_next = mem_read_data_valid_reg;

    if (store_output || !mem_read_data_valid_reg) begin
        // output data not valid OR currently being transferred
        if (!empty) begin
            // not empty, perform read
            read = 1'b1;
            mem_read_data_valid_next = 1'b1;
            rd_ptr_next = rd_ptr_reg + 1;
        end else begin
            // empty, invalidate
            mem_read_data_valid_next = 1'b0;
        end
    end
end

always @(posedge clk) begin
    if (rst) begin
        rd_ptr_reg <= {ADDR_WIDTH+1{1'b0}};
        mem_read_data_valid_reg <= 1'b0;
    end else begin
        rd_ptr_reg <= rd_ptr_next;
        mem_read_data_valid_reg <= mem_read_data_valid_next;
    end

    rd_addr_reg <= rd_ptr_next;

    if (read) begin
        mem_read_data_reg <= mem[rd_addr_reg[ADDR_WIDTH-1:0]];
    end
end

// Output register
always @* begin
    store_output = 1'b0;

    m_axis_tvalid_next = m_axis_tvalid_reg;

    if (m_axis_tready || !m_axis_tvalid) begin
        store_output = 1'b1;
        m_axis_tvalid_next = mem_read_data_valid_reg;
    end
end

always @(posedge clk) begin
    if (rst) begin
        m_axis_tvalid_reg <= 1'b0;
    end else begin
        m_axis_tvalid_reg <= m_axis_tvalid_next;
    end

    if (store_output) begin
        m_axis_reg <= mem_read_data_reg;
    end
end

endmodule
