module multi0keep(
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
// as opposed to the regular multi0, we always expose the buffer content
assign out = buffer;

endmodule