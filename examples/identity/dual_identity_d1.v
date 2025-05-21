module identity_d1 (
    input              clk, 
    input       [31:0] a,
    input       [31:0] b,
    output reg  [31:0] s1,
    output reg  [31:0] s2,
);  
    // One register delay
    always @(posedge clk) begin
        s1 <= a;
        s2 <= b;
    end
endmodule
