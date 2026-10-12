module use_without_valid_bug (
    input             clk,
    input   [31:0]    data,
    input             data_val,
    output reg [31:0] sum,
);

    always @(posedge clk) begin
        sum <= sum + data;
    end
endmodule