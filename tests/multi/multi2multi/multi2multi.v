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

module multi0(
	input wire clock,
	input wire reset,
	input wire start,
	input wire [31:0] inp,
	output wire done,
	output wire [31:0] out);

reg [31:0] buffer;
always @(posedge clock)
	if(start) buffer <= inp;

reg [1:0] delay;
always @(posedge clock)
	if(reset)     delay <= 2'h1;
	// else if(done) delay <= delay + 4'h1;

reg [3:0] counter;
always @(posedge clock)
	if(start) counter <= 4'h0;
	else      counter <= counter + 4'h1;

reg running;
always @(posedge clock)
	if(reset)      running <= 1'h0;
	else if(start) running <= 1'h1;
	else if(done)  running <= 1'h0;

assign done = running & (counter == {2'h0, delay});
assign out = (done)? buffer : 32'h0;

endmodule