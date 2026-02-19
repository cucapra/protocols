################################################################################
##
## Filename: 	Makefile
##
## Project:	Verilog Tutorial Example file
##
## Purpose:	Builds the Verilator request-walker bus slave example
##
## Targets:
##
##	The (default) or all target will build a verilator simulation for the
##	Request Walker.
##
##	clean	Removes all build products
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Written and distributed by Gisselquist Technology, LLC
##
## This program is hereby granted to the public domain.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.
##
################################################################################
##
##
.PHONY: all
all: reqwalker_tb

VERILATOR=verilator
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e "s/^.*=\s*//"')
VINC := $(VERILATOR_ROOT)/include

obj_dir/Vreqwalker.cpp: reqwalker.v
	$(VERILATOR) --trace -Wall -cc reqwalker.v

obj_dir/Vreqwalker__ALL.a: obj_dir/Vreqwalker.cpp
	make --no-print-directory -C obj_dir -f Vreqwalker.mk

reqwalker_tb: reqwalker.cpp obj_dir/Vreqwalker__ALL.a
	g++ -I$(VINC) -I obj_dir $(VINC)/verilated.cpp	\
		$(VINC)/verilated_vcd_c.cpp reqwalker.cpp	\
		obj_dir/Vreqwalker__ALL.a -o reqwalker_tb

.PHONY: clean
clean:
	rm -rf obj_dir/ reqwalker_tb reqwalker.vcd reqwalker_cvr/ reqwalker_prf/
