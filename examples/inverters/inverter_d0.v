module inverter_d0 (
    input         clk, 
    input  [31:0] a, 
    output [31:0] s,
);

    assign s = ~a;
endmodule