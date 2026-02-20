////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	reqwalker.v
//
// Project:	Verilog Tutorial Example file
//
// Purpose:	To walk an active LED back and forth across a set of 8 LEDs
//		upon request.  This is a demo design.  It should be easy enough
//	to adjust it to "N" LED's, or whatever your hardware has.
//
// 	This demo design is also broken in several ways.  This is on purpose.
// 	Follow the coursework, and we'll find and fix the bugs in this design.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Written and distributed by Gisselquist Technology, LLC
//
// This program is hereby granted to the public domain.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.
//
////////////////////////////////////////////////////////////////////////////////
//
//
module	reqwalker(i_clk,
		i_cyc, i_stb, i_we, i_addr, i_data,
		o_stall, o_ack, o_data,
		o_led);
	input	wire		i_clk;
	//
	// Our wishbone bus interface
	input	wire		i_cyc, i_stb, i_we;
	input	wire		i_addr;
	input	wire	[31:0]	i_data;
	//
	output	wire		o_stall;
	output	reg		o_ack;
	output	wire	[31:0]	o_data;
	//
	// The output LED
	output	reg	[5:0]	o_led;

	wire		busy;
	reg	[3:0]	state;

	initial	state = 0;
	always @(posedge i_clk)
	if ((i_stb)&&(i_we)&&(!o_stall))
		state <= 4'h1;
	else if (state >= 4'd11)
		state <= 4'h0;
	else if (state != 0)
		state <= state + 1'b1;

	always @(posedge i_clk)
	case(state)
	4'h1: o_led <= 6'b00_0001;
	4'h2: o_led <= 6'b00_0010;
	4'h3: o_led <= 6'b00_0100;
	4'h4: o_led <= 6'b00_1000;
	4'h5: o_led <= 6'b01_0000;
	4'h6: o_led <= 6'b10_0000;
	4'h7: o_led <= 6'b01_0000;
	4'h8: o_led <= 6'b00_1000;
	4'h9: o_led <= 6'b00_0100;
	4'ha: o_led <= 6'b00_0010;
	4'hb: o_led <= 6'b00_0001;
	default: o_led <= 6'b00_0000;
	endcase

	assign	busy = (state != 0);

	initial	o_ack = 1'b0;
	always @(posedge i_clk)
		o_ack <= (i_stb)&&(!o_stall);

	assign	o_stall = (busy)&&(i_we);
	assign	o_data = { 28'h0, state };

	// Verilator lint_off UNUSED
	wire	[33:0]	unused;
	assign	unused = { i_cyc, i_addr, i_data };
	// Verilator lint_on  UNUSED

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	//////
	//
	// Bus properties
	//
	initial	assume(!i_cyc);

	// i_stb is only allowed if i_cyc is also true
	always @(*)
	if (!i_cyc)
		assume(!i_stb);

	// When i_cyc goes high, so too should i_stb
	// Since this is an assumption, no f_past_valid is required
	always @(posedge i_clk)
	if ((!$past(i_cyc))&&(i_cyc))
		assume(i_stb);

	always @(posedge i_clk)
	if (($past(i_stb))&&($past(o_stall)))
	begin
		assume(i_stb);
		assume(i_we == $past(i_we));
		assume(i_addr == $past(i_addr));
		if (i_we)
			assume(i_data == $past(i_data));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_stb))&&(!$past(o_stall)))
		assert(o_ack);

	//////
	//
	// Design properties
	//
	always @(*)
		assert(state <= 4'd11);

	always @(*)
	begin
		case(state)
		4'h1: assert(o_led == 6'b00_0001);
		4'h2: assert(o_led == 6'b00_0010);
		4'h3: assert(o_led == 6'b00_0100);
		4'h4: assert(o_led == 6'b00_1000);
		4'h5: assert(o_led == 6'b01_0000);
		4'h6: assert(o_led == 6'b10_0000);
		4'h7: assert(o_led == 6'b01_0000);
		4'h8: assert(o_led == 6'b00_1000);
		4'h9: assert(o_led == 6'b00_0100);
		4'ha: assert(o_led == 6'b00_0010);
		4'hb: assert(o_led == 6'b00_0001);
		endcase
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_stb))&&($past(i_we))&&($past(!o_stall)))
	begin
		assert(state == 1);
		assert(busy);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(busy))&&($past(state < 4'hb)))
		assert(state == $past(state)+1);

	always @(posedge i_clk)
	if (f_past_valid)
		cover((!busy)&&($past(busy)));
`endif
endmodule
