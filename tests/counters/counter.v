module counter (
    input             clk,  
    input      [63:0] a,
    output reg [63:0] s
);
    always @(posedge clk) begin
        if (s >= a) begin
            s <= 0; 
        end else begin
            s <= s + 1;
        end
    end
endmodule
