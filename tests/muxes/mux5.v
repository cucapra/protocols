module comb_mux5(
  input  clk,
  input  [7:0] in0, in1, in2, in3, in4,
  input  [2:0] sel,
  output [7:0] y
);

  // Returns all 0s for the `default` branch of the case statement
  always_comb begin
    case ( sel )
      3'd0 : y = in0;
      3'd1 : y = in1;
      3'd2 : y = in2;
      3'd3 : y = in3;
      3'd4 : y = in4;
      default : y = 8'b00000000;
    endcase
  end

endmodule