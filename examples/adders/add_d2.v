module adder_d2 (
    input             clk,
    input [31:0]      A,
    input [31:0]      B,
    output reg [31:0] S
);

    reg [31:0] r1;

    always @(posedge clk) begin
        r1 <= A + B;
        S  <= r1;
    end

endmodule