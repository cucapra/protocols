module toy_receiver_0 (
    input              clk, 
    input       [7:0] data,
    input            valid,
    output reg       ready
);  

    always @(*) begin
        // raise ready whenever valid is raised
        ready = valid;
    end
endmodule