module multiplier_d1 (
    input              clk, 
    input       [31:0] a,
    input       [31:0] b,
    output reg  [31:0] s     
);
    wire [31:0] res;

    assign res = a * b;

    always @(posedge clk) begin
        s <= res;
    end
endmodule