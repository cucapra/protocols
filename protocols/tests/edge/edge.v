module edge_detector (
    input clk,
    input signal,
    input enable,
    output reg edge_detected
);

reg signal_prev;

always @(posedge clk) begin
    signal_prev <= signal;
    
    if (enable) begin
        // Detect rising edge: current is 1, previous was 0
        edge_detected <= signal && !signal_prev;
    end else begin
        edge_detected <= 0;
    end
end

endmodule
