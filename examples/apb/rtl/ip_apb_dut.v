`timescale 1ns/1ps
// This Verilog file is only used for renaming pins.
module ip_apb_dut(
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

    apb_slave #(.DW(32), .AW(5)) inst (
        .pclk      (clk),
        .presetn   (PRESETn),
        .i_paddr   (PADDR[4:0]),
        .i_pwrite  (PWRITE),
        .i_psel    (PSEL),
        .i_penable (PENABLE),
        .i_pwdata  (PWDATA),
        .i_pstrb   (PSTRB),
        .o_prdata  (PRDATA),
        .o_pslverr (PSLVERR),
        .o_pready  (PREADY),
        .o_hw_ctl  (),
        .i_hw_sts  (1'b0)
    );
endmodule
