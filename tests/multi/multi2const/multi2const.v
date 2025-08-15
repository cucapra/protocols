// wraps a multi cycle circuit and is itself multi cycle
module multi2const(
	input wire clock,
	input wire reset,
	input wire start,
	input wire [63:0] inp,
//	output wire done,
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

reg [31:0] msb_buffer, lsb_buffer;
always @(posedge clock) if(msb_done) msb_buffer <= msb_out;
always @(posedge clock) if(lsb_done) lsb_buffer <= lsb_out;

// since this unit has predictable timing, no "done" signal is needed
//reg [3:0] counter;
//always @(posedge clock)
//	if(start) counter <= 4'h0;
//	else      counter <= counter + 4'h1;
//
//reg running;
//always @(posedge clock)
//	if(reset)      running <= 1'h0;
//	else if(start) running <= 1'h1;
//	else if(done)  running <= 1'h0;


//assign done = (counter == 4'h3) & running;
assign out  =
	( msb_done &  lsb_done)? {msb_out, lsb_out} :
	( msb_done & !lsb_done)? {msb_out, lsb_buffer} :
	(!msb_done &  lsb_done)? {msb_buffer, lsb_out} :
	                         {msb_buffer, lsb_buffer};

endmodule