module toy_receiver_2 (
    input              clk, 
    input       [7:0] data,
    input            valid,
    output reg       ready
);  
    reg delay1;


    always @(posedge clk) begin
        delay1 <= valid;
        ready <= delay1;
    end
endmodule