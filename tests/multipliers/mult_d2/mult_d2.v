module multiplier_d2 (
    input             clk,
    input [31:0]      a,
    input [31:0]      b,
    output reg [31:0] s
);  
    wire [31:0] res;
    reg  [31:0] r1;
    assign res = a * b;

    always @(posedge clk) begin
        r1 <= res;
        s  <= r1;
    end
endmodule