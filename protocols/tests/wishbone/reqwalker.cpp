////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	redqalker.cpp
//
// Project:	Verilog Tutorial Example file
//
// Purpose:	This is an example Verilator test bench driver file reqwalker
//		module.
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
#include <stdio.h>
#include <stdlib.h>
#include "Vreqwalker.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

int	tickcount = 0;
Vreqwalker	*tb;
VerilatedVcdC	*tfp;

void	tick(void) {
	tickcount++;

	tb->eval();
	if (tfp)
		tfp->dump(tickcount * 10 - 2);
	tb->i_clk = 1;
	tb->eval();
	if (tfp)
		tfp->dump(tickcount * 10);
	tb->i_clk = 0;
	tb->eval();
	if (tfp) {
		tfp->dump(tickcount * 10 + 5);
		tfp->flush();
	}
}

unsigned wb_read(unsigned a) {
	tb->i_cyc = tb->i_stb = 1;
	tb->i_we  = 0;
	tb->i_addr= a;
	// Make the request
	while(tb->o_stall)
		tick();
	tick();
	tb->i_stb = 0;
	// Wait for the ACK
	while(!tb->o_ack)
		tick();
	// Idle the bus, and read the response
	tb->i_cyc = 0;
	return tb->o_data;
}

void wb_write(unsigned a, unsigned v) {
	tb->i_cyc = tb->i_stb = 1;
	tb->i_we  = 1;
	tb->i_addr= a;
	tb->i_data= v;
	// Make the bus request
	while(tb->o_stall)
		tick();
	tick();
	tb->i_stb = 0;
	// Wait for the acknowledgement
	while(!tb->o_ack)
		tick();
	// Idle the bus and return
	tb->i_cyc = tb->i_stb = 0;
}

int main(int argc, char **argv) {
	int	last_led, last_state = 0, state = 0;

	// Call commandArgs first!
	Verilated::commandArgs(argc, argv);

	// Instantiate our design
	tb = new Vreqwalker;

	// Generate a trace
	Verilated::traceEverOn(true);
	tfp = new VerilatedVcdC;
	tb->trace(tfp, 99);
	tfp->open("reqwalker.vcd");

	last_led = tb->o_led;

	// Read from the current state
	printf("Initial state is: 0x%02x\n",
		wb_read(0));

	for(int cycle=0; cycle<2; cycle++) {
		// Wait five clocks
		for(int i=0; i<5; i++)
			tick();

		// Start the LEDs cycling
		wb_write(0,0);
		tick();

		while((state = wb_read(0))!=0) {
			if ((state != last_state)
				||(tb->o_led != last_led)) {
				printf("%6d: State #%2d ",
					tickcount, state);
				for(int j=0; j<6; j++) {
					if(tb->o_led & (1<<j))
						printf("O");
					else
						printf("-");
				} printf("\n");
			} tick();

			last_state = state;
			last_led = tb->o_led;
		}
	}

	tfp->close();
	delete tfp;
	delete tb;
}
