module counter(
    input clk,        
    output reg [6:0] count
);

    always @(posedge clk) begin
        if (count == 100) begin
            count <= 7'b0; 
        end else begin
            count <= count + 1;
        end
    end
endmodule