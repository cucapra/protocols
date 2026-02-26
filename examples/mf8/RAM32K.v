/*
 * Copyright 2018 MicroFPGA UG
 * Apache 2.0 License
 */

module RAM32K (clk, addr, din, dout, we);

input clk;
input we;
input [14:0] addr;
input  [7:0] din;
output [7:0] dout;

// RAM
`ifdef SIM

reg [7:0] mem [0:32*1024-1];
reg [7:0] dout;
initial $readmemh("riscv.mem", mem);

always @(posedge clk) begin
	if (we) mem[addr] <= din;
	dout <= mem[addr];
end

`else

// SBRAM
wire [15:0] SBRAM_Dataout;
reg DelayOdd;
always @(posedge clk) begin
	DelayOdd <= addr[0];
end
assign dout = DelayOdd? SBRAM_Dataout[15:8] : SBRAM_Dataout[7:0];

SB_SPRAM256KA ram (
    .ADDRESS(addr[14:1]),
    .DATAIN({din, din}),
    .MASKWREN({addr[0], addr[0], ~addr[0], ~addr[0]}),
    .WREN(we),
    .CHIPSELECT(1'b1),
    .CLOCK(clk),
    .STANDBY(1'b0),
    .SLEEP(1'b0),
    .POWEROFF(1'b1),
    .DATAOUT(SBRAM_Dataout)
);

`endif

endmodule