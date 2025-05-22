module identity_d2 (
    input              clk,
    input       [31:0] a,
    output reg  [31:0] s
);  
    // Two register delay
    reg  [31:0] r1;

    always @(posedge clk) begin
        r1 <= a;
        s  <= r1;
    end
endmodule