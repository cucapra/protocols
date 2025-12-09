// From https://github.com/ngernest/rtl-repair/blob/asplos24/benchmarks/fpga-debugging/axis-fifo-d12/axis_fifo.v

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
    parameter ADDR_WIDTH = 2,
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter LAST_ENABLE = 1,
    parameter ID_ENABLE = 1,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 1,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1,
    parameter FRAME_FIFO = 1,
    parameter USER_BAD_FRAME_VALUE = 1'b1,
    parameter USER_BAD_FRAME_MASK = 1'b1,
    parameter DROP_BAD_FRAME = 0,
    parameter DROP_WHEN_FULL = 1
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


/* DISABLED Simulation Only Construct
// check configuration
initial begin
    if (FRAME_FIFO && !LAST_ENABLE) begin
        $error("Error: FRAME_FIFO set requires LAST_ENABLE set");
        $finish;
    end

    if (DROP_BAD_FRAME && !FRAME_FIFO) begin
        $error("Error: DROP_BAD_FRAME set requires FRAME_FIFO set");
        $finish;
    end

    if (DROP_WHEN_FULL && !FRAME_FIFO) begin
        $error("Error: DROP_WHEN_FULL set requires FRAME_FIFO set");
        $finish;
    end

    if (DROP_BAD_FRAME && (USER_BAD_FRAME_MASK & {USER_WIDTH{1'b1}}) == 0) begin
        $error("Error: Invalid USER_BAD_FRAME_MASK value");
        $finish;
    end
end
*/

localparam KEEP_OFFSET = DATA_WIDTH;
localparam LAST_OFFSET = KEEP_OFFSET + (KEEP_ENABLE ? KEEP_WIDTH : 0);
localparam ID_OFFSET   = LAST_OFFSET + (LAST_ENABLE ? 1          : 0);
localparam DEST_OFFSET = ID_OFFSET   + (ID_ENABLE   ? ID_WIDTH   : 0);
localparam USER_OFFSET = DEST_OFFSET + (DEST_ENABLE ? DEST_WIDTH : 0);
localparam WIDTH       = USER_OFFSET + (USER_ENABLE ? USER_WIDTH : 0);

reg [ADDR_WIDTH:0] wr_ptr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_next;
reg [ADDR_WIDTH:0] wr_ptr_cur_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] wr_ptr_cur_next;
reg [ADDR_WIDTH:0] wr_addr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_reg = {ADDR_WIDTH+1{1'b0}};
reg [ADDR_WIDTH:0] rd_ptr_next;
reg [ADDR_WIDTH:0] rd_addr_reg = {ADDR_WIDTH+1{1'b0}};

reg [WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0];
reg [WIDTH-1:0] mem_read_data_reg;
reg mem_read_data_valid_reg = 1'b0;
reg mem_read_data_valid_next;

wire [WIDTH-1:0] s_axis;

reg [WIDTH-1:0] m_axis_reg;
reg m_axis_tvalid_reg = 1'b0;
reg m_axis_tvalid_next;

// full when first MSB different but rest same
wire full = ((wr_ptr_reg[ADDR_WIDTH] != rd_ptr_reg[ADDR_WIDTH]) &&
             (wr_ptr_reg[ADDR_WIDTH-1:0] == rd_ptr_reg[ADDR_WIDTH-1:0]));
wire full_cur = ((wr_ptr_cur_reg[ADDR_WIDTH] != rd_ptr_reg[ADDR_WIDTH]) &&
                 (wr_ptr_cur_reg[ADDR_WIDTH-1:0] == rd_ptr_reg[ADDR_WIDTH-1:0]));
// empty when pointers match exactly
wire empty = wr_ptr_reg == rd_ptr_reg;
// overflow within packet
wire full_wr = ((wr_ptr_reg[ADDR_WIDTH] != wr_ptr_cur_reg[ADDR_WIDTH]) &&
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

assign s_axis_tready = FRAME_FIFO ? (!full_cur || full_wr || DROP_WHEN_FULL) : !full;

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


/* DISABLED Simulation Only Construct
always @(posedge clk) begin
    if (!rst) begin
        if ((s_axis_tvalid && s_axis_tready) && !(m_axis_tvalid && m_axis_tready) && wr_ptr_cur_reg[ADDR_WIDTH] != rd_ptr_reg[ADDR_WIDTH] && wr_ptr_cur_reg[ADDR_WIDTH-1:0] == rd_ptr_reg[ADDR_WIDTH-1:0])
            $error("buffer overflow");
    end
end
*/

// Write logic - PUSH transaction control
always @* begin
    write = 1'b0;  // Default: IDLE (no push)

    drop_frame_next = drop_frame_reg;
    overflow_next = 1'b0;
    bad_frame_next = 1'b0;
    good_frame_next = 1'b0;

    wr_ptr_next = wr_ptr_reg;           // Default: IDLE (pointers unchanged)
    wr_ptr_cur_next = wr_ptr_cur_reg;   // Default: IDLE (pointers unchanged)

    if (s_axis_tready && s_axis_tvalid) begin
        // AXI handshake succeeded - transaction requested
        if (!FRAME_FIFO) begin
            // PUSH: normal FIFO mode - unconditional write
            write = 1'b1;
            wr_ptr_next = wr_ptr_reg + 1;
        end else if (full_cur || full_wr || drop_frame_reg) begin
            // IDLE (drop): full, packet overflow, or currently dropping frame
            // drop frame - no write to memory
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
                //if (DROP_BAD_FRAME && (USER_BAD_FRAME_MASK & s_axis_tuser == USER_BAD_FRAME_VALUE)) begin
                if (DROP_BAD_FRAME && USER_BAD_FRAME_MASK & ~(s_axis_tuser ^ USER_BAD_FRAME_VALUE)) begin
                    // bad packet, reset write pointer
                    wr_ptr_cur_next = wr_ptr_reg;
                    bad_frame_next = 1'b1;
                end else begin
                    // PUSH complete: good packet, commit write pointer
                    wr_ptr_next = wr_ptr_cur_reg + 1;
                    good_frame_next = 1'b1;
                end
            end
        end
    end
    // else: IDLE - no handshake, no write
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
        mem[wr_addr_reg[ADDR_WIDTH-1:0]] <= s_axis;
    end
    // else: IDLE - no memory write
end

// Read logic - POP transaction control
always @* begin
    read = 1'b0;  // Default: IDLE (no pop)

    rd_ptr_next = rd_ptr_reg;  // Default: IDLE (pointer unchanged)

    mem_read_data_valid_next = mem_read_data_valid_reg;

    if (store_output || !mem_read_data_valid_reg) begin
        // output data not valid OR currently being transferred
        if (!empty) begin
            // POP: not empty, perform read from memory
            read = 1'b1;
            mem_read_data_valid_next = 1'b1;
            rd_ptr_next = rd_ptr_reg + 1;
        end else begin
            // IDLE: empty FIFO, invalidate read data
            mem_read_data_valid_next = 1'b0;
        end
    end
    // else: IDLE - output stage has valid data and not being consumed
end

always @(posedge clk) begin
    if (rst) begin
        // RESET: Initialize read-side registers
        rd_ptr_reg <= {ADDR_WIDTH+1{1'b0}};
        mem_read_data_valid_reg <= 1'b0;
    end else begin
        // Update read state (POP or IDLE)
        rd_ptr_reg <= rd_ptr_next;
        mem_read_data_valid_reg <= mem_read_data_valid_next;
    end

    rd_addr_reg <= rd_ptr_next;

    if (read) begin
        // POP: Read data from memory to intermediate register
        mem_read_data_reg <= mem[rd_addr_reg[ADDR_WIDTH-1:0]];
    end
    // else: IDLE - no memory read
end

// Output register - POP completion stage
always @* begin
    store_output = 1'b0;  // Default: IDLE (no output update)

    m_axis_tvalid_next = m_axis_tvalid_reg;

    if (m_axis_tready || !m_axis_tvalid) begin
        // POP complete: downstream ready or no valid data, update output
        store_output = 1'b1;
        m_axis_tvalid_next = mem_read_data_valid_reg;
    end
    // else: IDLE - output blocked by downstream not ready
end

always @(posedge clk) begin
    if (rst) begin
        // RESET: Initialize output-side registers
        m_axis_tvalid_reg <= 1'b0;
    end else begin
        // Update output valid (POP or IDLE)
        m_axis_tvalid_reg <= m_axis_tvalid_next;
    end

    if (store_output) begin
        // POP complete: Transfer data to output register
        m_axis_reg <= mem_read_data_reg;
    end
    // else: IDLE - output register unchanged
end

endmodule
