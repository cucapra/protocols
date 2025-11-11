module bit_truncation_sha_fixed (
    input             clk,
    input      [63:0] right,
    output reg [41:0] left
);
    // FIX: Perform the shift first in 64 bits, then cast down to 42 bits
    always @(posedge clk) begin
        left <= 42'(right >> 6);
    end
endmodule
