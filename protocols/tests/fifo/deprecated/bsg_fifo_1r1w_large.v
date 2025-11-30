module bsg_fifo_1r1w_large (
	clk_i,
	reset_i,
	data_i,
	v_i,
	ready_and_o,
	v_o,
	data_o,
	yumi_i
);
	parameter width_p = 0;
	parameter els_p = 0;
	input clk_i;
	input reset_i;
	input [width_p - 1:0] data_i;
	input v_i;
	output wire ready_and_o;
	output wire v_o;
	output wire [width_p - 1:0] data_o;
	input yumi_i;
	wire [(width_p * 2) - 1:0] data_sipo;
	wire [1:0] valid_sipo;
	wire [1:0] yumi_cnt_sipo;
	bsg_serial_in_parallel_out #(
		.width_p(width_p),
		.els_p(3),
		.out_els_p(2)
	) sipo(
		.clk_i(clk_i),
		.reset_i(reset_i),
		.valid_i(v_i),
		.data_i(data_i),
		.ready_and_o(ready_and_o),
		.valid_o(valid_sipo),
		.data_o(data_sipo),
		.yumi_cnt_i(yumi_cnt_sipo)
	);
	wire [(2 * width_p) - 1:0] big_data_lo;
	wire big_valid;
	wire big_full_lo;
	wire big_empty_lo;
	wire big_enq;
	wire big_deq;
	reg big_deq_r;
	always @(posedge clk_i) big_deq_r <= big_deq;
	bsg_fifo_1rw_large #(
		.width_p(width_p * 2),
		.els_p(els_p >> 1)
	) big1p(
		.clk_i(clk_i),
		.reset_i(reset_i),
		.data_i(data_sipo),
		.v_i(big_valid),
		.enq_not_deq_i(big_enq),
		.full_o(big_full_lo),
		.empty_o(big_empty_lo),
		.data_o(big_data_lo)
	);
	wire [(2 * width_p) - 1:0] little_data_rot;
	wire [1:0] little_valid;
	wire [1:0] little_ready;
	wire [1:0] little_ready_rot;
	wire [1:0] little_valid_rot;
	wire [1:0] valid_int;
	wire bypass_mode = (~big_deq_r & little_ready[0]) & big_empty_lo;
	wire can_spill = ~big_full_lo & ~bypass_mode;
	wire emergency = (&little_ready_rot & ~big_empty_lo) & ~big_deq_r;
	wire will_spill = (can_spill & (&valid_sipo)) & ~emergency;
	assign big_deq = (~will_spill & ~big_empty_lo) & (big_deq_r ? ~|valid_int : &little_ready_rot);
	assign big_valid = will_spill | big_deq;
	assign big_enq = will_spill;
	wire [(2 * width_p) - 1:0] little_data = (big_deq_r ? big_data_lo : data_sipo);
	wire [1:0] bypass_vector = valid_sipo & {bypass_mode, bypass_mode};
	assign little_valid = (big_deq_r ? 2'b11 : bypass_vector);
	wire [1:0] cnt;
	bsg_thermometer_count #(.width_p(2)) thermo(
		.i(little_ready & bypass_vector),
		.o(cnt)
	);
	assign yumi_cnt_sipo = (will_spill ? 2'b10 : cnt);
	bsg_round_robin_2_to_2 #(.width_p(width_p)) rr222(
		.clk_i(clk_i),
		.reset_i(reset_i),
		.data_i(little_data),
		.v_i(little_valid),
		.ready_o(little_ready),
		.data_o(little_data_rot),
		.v_o(little_valid_rot),
		.ready_i(little_ready_rot)
	);
	wire [(2 * width_p) - 1:0] data_int;
	wire [1:0] yumi_int;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < 2; _gv_i_1 = _gv_i_1 + 1) begin : twofer
			localparam i = _gv_i_1;
			bsg_two_fifo #(.width_p(width_p)) little(
				.clk_i(clk_i),
				.reset_i(reset_i),
				.ready_param_o(little_ready_rot[i]),
				.data_i(little_data_rot[i * width_p+:width_p]),
				.v_i(little_valid_rot[i]),
				.v_o(valid_int[i]),
				.data_o(data_int[i * width_p+:width_p]),
				.yumi_i(yumi_int[i])
			);
		end
	endgenerate
	bsg_round_robin_n_to_1 #(
		.width_p(width_p),
		.num_in_p(2),
		.strict_p(1)
	) round_robin_n_to_1(
		.clk_i(clk_i),
		.reset_i(reset_i),
		.data_i(data_int),
		.v_i(valid_int),
		.yumi_o(yumi_int),
		.data_o(data_o),
		.v_o(v_o),
		.tag_o(),
		.yumi_i(yumi_i)
	);
	wire [31:0] num_elements_debug = ((((((2 * big1p.num_elements_debug) + valid_int[0]) + valid_int[1]) + sipo.valid_r[0]) + sipo.valid_r[1]) + !little_ready_rot[0]) + !little_ready_rot[1];
endmodule
module bsg_fifo_1r1w_large__abstract;
	
endmodule
