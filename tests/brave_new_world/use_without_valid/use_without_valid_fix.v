module use_without_valid_fix (
    input             clk,
    input   [31:0]    data,
    input             data_val,
    output reg [31:0] sum,
);

    always @(posedge clk) begin
        if (data_val) sum <= sum + data;
        else sum <= sum;
    end
endmodule