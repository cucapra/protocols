// An ALU with a 1-cycle delay, 
// supporting addition / subtraction / bitwise AND / bitwise OR
module alu_d1 (
    input              clk, 
    input       [31:0] a,
    input       [31:0] b,
    input       [1:0] op,
    output reg  [31:0] s
);  

    always @(posedge clk) begin
        case(op)
          2'b00: s <= a + b;
          2'b01: s <= a - b;
          2'b10: s <= a & b;
          2'b11: s <= a | b;
        endcase
    end
endmodule