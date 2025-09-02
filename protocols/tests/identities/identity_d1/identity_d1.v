module identity_d1 (
    input              clk, 
    input       [31:0] a,
    output reg  [31:0] s
);  
    // One register delay
    always @(posedge clk) begin
        s <= a;
    end
endmodule
