module counter (
    clk,
    trigger,
    reset,
    sm,
    limit
);

  // DECLARATIONS
  input clk;
  input trigger;
  input reset;
  output [4:0] sm;
  input [4:0] limit;

  reg [4:0] sm;

  // CODE

  initial begin
    sm = 5'b00000;
  end

  always @(posedge clk) begin
    #1
    if (trigger == 1'b1) #4 sm = 5'b00001;
    else if (reset == 1'b1) #4 sm = 5'b00000;
    else if ((sm >= 5'b00001) && (sm < limit)) #4 sm = sm + 5'b00001;
  end

endmodule
