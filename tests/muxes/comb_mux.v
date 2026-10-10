module comb_mux(
  input       clk,
  input [7:0] a,
  input [7:0] b,
  input       sel,
  output [7:0] y
);
  assign y = sel ? b : a;
endmodule