module multiplier_d1 (
    input              clk, 
    input       [31:0] a,
    input       [31:0] b,
    output reg  [31:0] s     
);
    wire [31:0] res;
    reg  [31:0] s0;

    assign res = a * b;

    always @(posedge clk) begin
        s0 <= res;
        s <= s0;
    end
endmodule