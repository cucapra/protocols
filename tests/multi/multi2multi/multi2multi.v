// wraps a multi cycle circuit and is itself multi cycle
module multi2multi(
	input wire clock,
	input wire reset,
	input wire start,
	input wire [63:0] inp,
	output wire done,
	output wire [63:0] out);


wire lsb_done, msb_done;
wire [31:0] lsb_out, msb_out;


multi0 lsb_unit(
	.clock(clock), .reset(reset), .start(start),
	.inp(inp[31:0]), .done(lsb_done), .out(lsb_out)
);
multi0 msb_unit(
	.clock(clock), .reset(reset), .start(start),
	.inp(inp[63:32]), .done(msb_done), .out(msb_out)
);


reg [31:0] buffer;
always @(posedge clock)
	if(msb_done) buffer <= msb_out;
	else if(lsb_done) buffer <= lsb_out;

reg both_running;
always @(posedge clock)
	if(reset)      both_running <= 1'h0;
	else if(start) both_running <= 1'h1;
	else if(lsb_done | msb_done)  both_running <= 1'h0;

assign done = 
	(msb_done & lsb_done) |
	(!both_running & lsb_done) |
	(!both_running & msb_done);

assign out =
	(msb_done & lsb_done)?      {msb_out, lsb_out} :
	(msb_done & !both_running)? {msb_out, buffer} :
	                            {buffer, lsb_out};

endmodule