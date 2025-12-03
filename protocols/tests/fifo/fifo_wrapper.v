// Wrapper module that instantiates the `bsg_fifo_1rw_large` module (in `bsg_fifo_1rw_large.v`) with explicit parameters
// This ensures width_p is set to 32 bits in `bsg_fifo_1rw_large.v`, matching the `u32` type in our Protocol specification 

module fifo_wrapper (
    input clk_i,
    input reset_i,
    input [31:0] data_i,
    input v_i,
    input enq_not_deq_i,
    output full_o,
    output empty_o,
    output [31:0] data_o
);

    // Instantiate the FIFO with explicit 32-bit width and 16 elements
    bsg_fifo_1rw_large #(
        .width_p(32),
        .els_p(16),
        .verbose_p(0)
    ) fifo_inst (
        .clk_i(clk_i),
        .reset_i(reset_i),
        .data_i(data_i),
        .v_i(v_i),
        .enq_not_deq_i(enq_not_deq_i),
        .full_o(full_o),
        .empty_o(empty_o),
        .data_o(data_o)
    );

endmodule
