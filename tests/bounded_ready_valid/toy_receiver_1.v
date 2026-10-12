module toy_receiver_0 (
    input              clk, 
    input       [7:0] data,
    input            valid,
    output reg       ready
);  

    always @(posedge clk) begin
        ready <= valid;
    end
endmodule