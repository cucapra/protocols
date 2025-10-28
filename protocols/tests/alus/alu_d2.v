// An ALU with a 2-cycle delay, 
// supporting addition / subtraction / bitwise AND / bitwise OR
module alu_d2 (
    input              clk,
    input       [31:0] a,
    input       [31:0] b,
    input       [1:0] op,
    output reg  [31:0] s
);
    reg  [31:0] res;
    reg  [31:0] r1;

    // Combinational logic block
    // Computes the actual result
    always @(*) begin
        case(op)
          2'b00: res = a + b;
          2'b01: res = a - b;
          2'b10: res = a & b;
          2'b11: res = a | b;
        endcase
    end

    // Sequential logic block
    // Actually writes the result to the output parameter `s`
    // We need 2 registers here to ensure a 2-cycle delay
    always @(posedge clk) begin
        r1 <= res;
        s  <= r1;
    end
endmodule
