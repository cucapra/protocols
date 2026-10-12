module adder_d1 (
    input              clk, 
    input       [31:0] a,
    input       [31:0] b,
    output reg  [31:0] s
);  

    always @(posedge clk) begin
        s <= a + b;
    end
endmodule