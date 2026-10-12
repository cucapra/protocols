// wraps a multi cycle circuit and is itself multi cycle
module multi0keep2const(
	input wire clock,
	input wire reset,
	input wire start,
	input wire [63:0] inp,
	output wire [63:0] out);

wire lsb_done, msb_done;
wire [31:0] lsb_out, msb_out;

multi0keep lsb_unit(
	.clock(clock), .reset(reset), .start(start),
	.inp(inp[31:0]), .done(lsb_done), .out(lsb_out)
);
multi0keep msb_unit(
	.clock(clock), .reset(reset), .start(start),
	.inp(inp[63:32]), .done(msb_done), .out(msb_out)
);

// no need to buffer as the multi cycle unit keeps the output constant
assign out = { msb_out, lsb_out };

endmodule