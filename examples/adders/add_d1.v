module adder_d1 (
    input              clk, 
    input       [31:0] A,
    input       [31:0] B,
    output reg  [31:0] S
);
    always @(posedge clk) begin
        sum <= A + B;
    end

endmodule