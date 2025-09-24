module sha_truncation_bug (
    input             clk,
    input      [63:0] right,
    output reg [41:0] left
);
    // BUG: cast applied after shift, so the top 22 bits are silently dropped
    always @(posedge clk) begin
        left <= 42'(right) >> 6;
    end
endmodule