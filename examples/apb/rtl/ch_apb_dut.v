`timescale 1ns/1ps
// This Verilog file is only used for renaming pins (renaming `PCLK` to `clk`)
// and for setting the size of the memory.
module ch_apb_dut(
    input  wire        clk,
    input  wire        PRESETn,
    input  wire        PSEL,
    input  wire        PENABLE,
    input  wire        PWRITE,
    input  wire [31:0] PADDR,
    input  wire [31:0] PWDATA,
    input  wire [3:0]  PSTRB,
    input  wire [2:0]  PPROT,
    output wire [31:0] PRDATA,
    output wire        PREADY,
    output wire        PSLVERR
);

    apb_slave #(
        .ADDR_BUS_WIDTH(32),
        .DATA_BUS_WIDTH(32),
        .MEMSIZE(64),
        .MEM_BLOCK_SIZE(32),
        .RESET_VAL(0),
        .EN_WAIT_DELAY_FUNC(0)
    ) inst (
        .PRESETn (PRESETn),
        .PCLK    (clk),
        .PSEL    (PSEL),
        .PENABLE (PENABLE),
        .PWRITE  (PWRITE),
        .PADDR   (PADDR),
        .PWDATA  (PWDATA),
        .PRDATA  (PRDATA),
        .PREADY  (PREADY),
        .PSLVERR (PSLVERR)
    );
endmodule
