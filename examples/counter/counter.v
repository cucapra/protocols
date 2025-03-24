module counter(
    input clk,        
    output reg [6:0] c
);

    always @(posedge clk) begin
        if (c == 10) begin
            c <= 7'b0; 
        end else begin
            c <= c + 1;
        end
    end
endmodule