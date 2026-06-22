module toy_receiver_3 (
    input              clk, 
    input       [7:0] data,
    input            valid,
    output reg       ready
);  
    reg delay1;
    reg delay2;


    always @(posedge clk) begin
        delay1 <= valid;
        delay2 <= delay1;
        ready <= delay2;
    end
endmodule