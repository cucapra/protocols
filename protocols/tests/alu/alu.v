module ALU(
  input [3:0] A, // 4-bit input A
  input [3:0] B, // 4-bit input B
  input [2:0] OP, // 3-bit control input for operation selection
  output [3:0] Result // 4-bit output
);

// Define ALU operations based on OP
assign Result = (OP == 3'b000) ? A + B :
               (OP == 3'b001) ? A - B :
               (OP == 3'b010) ? A & B :
               (OP == 3'b011) ? A | B :
               (OP == 3'b100) ? A ^ B :
               4'b0000; // Default to zero for other OP values
  
endmodule