/* Keeps track of the history of events.  To be used with for_verilog.v 
This is a combinational circuit.  */

module history (
    trigger,
    reset,
    clk,
    sm
);

  //DECLARATIONS
  input trigger;
  input reset;
  input clk;

  output sm;

  reg sm;


  //CODE

  initial begin
    sm = 1'b0;
  end

  always @(posedge clk) begin
    #1
    if (trigger == 1'b1) #4 sm = 1'b1;
    else if (reset == 1'b1) #4 sm = 1'b0;
    else #1 sm = sm;
  end

endmodule
