// Wrapper Verilog module for renaming pins
module js_axis_dut (
    input  wire        clk,
    input  wire        aresetn,
    input  wire        tready,
    output wire        tvalid,
    output wire [31:0] tdata,
    output wire [3:0]  tkeep,
    output wire [3:0]  tstrb,
    output wire        tlast
);  
    // Note: The `xlnxstream_2018_3` module below doesn't have a `tkeep` port,
    // so we just drive `1111` onto `tkeep` for now
    assign tkeep = 4'b1111;

    xlnxstream_2018_3 #(
        .C_M_AXIS_TDATA_WIDTH(32),
        .C_M_START_COUNT(32)
    ) source (
        .M_AXIS_ACLK(clk),
        .M_AXIS_ARESETN(aresetn),
        .M_AXIS_TVALID(tvalid),
        .M_AXIS_TDATA(tdata),
        .M_AXIS_TSTRB(tstrb),
        .M_AXIS_TLAST(tlast),
        .M_AXIS_TREADY(tready)
    );
endmodule
