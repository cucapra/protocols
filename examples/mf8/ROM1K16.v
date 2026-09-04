/*
 * Copyright 2018 MicroFPGA UG
 * Apache 2.0 License
 */

module ROM1K16 (clk, addr, dout);

input clk;
input [8:0] addr;
output [15:0] dout;

// ROM with a single synchronous read port (can be mapped to Block RAM)
reg [15:0] mem [0:511];
reg [15:0] dout;
initial $readmemh("rv32i.mem", mem);
always @(posedge clk) begin
	dout <= mem[addr];
end

endmodule