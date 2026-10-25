module LoopDut (
    input clk,
    input [7:0] data,
    input flag,
    output reg ready,
    output reg [7:0] echo
);
    always @(posedge clk) begin
        ready <= !ready;
        echo <= data;
    end
endmodule
