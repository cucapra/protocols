/* This is a tristate driver.  
   If enable0 is high then busout = input0
   If enable1 is high then busout = input1
   Else busout = 0
*/

module buswire (
    enable0,
    enable1,
    input0,
    input1,
    busout
);

  input enable0;
  input enable1;
  input input0;
  input input1;

  output busout;

  wire busout;

  assign busout = enable0 ? input0 : (enable1 ? input1 : 1'b0);

endmodule
