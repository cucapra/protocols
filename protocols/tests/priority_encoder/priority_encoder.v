module priority_encoder (
    input clk,
    input [3:0] req,      // Request lines
    input lock,           // When high, locks current grant
    output reg [1:0] grant_id,
    output reg valid
);

reg [1:0] locked_id;
reg is_locked;

always @(posedge clk) begin
    if (lock && valid) begin
        // Lock the current grant
        locked_id <= grant_id;
        is_locked <= 1;
    end else if (!lock) begin
        is_locked <= 0;
    end
    
    if (is_locked && lock) begin
        // Stay with locked grant
        grant_id <= locked_id;
        valid <= req[locked_id];
    end else begin
        // Priority encode (highest priority = bit 3)
        if (req[3]) begin
            grant_id <= 2'd3;
            valid <= 1;
        end else if (req[2]) begin
            grant_id <= 2'd2;
            valid <= 1;
        end else if (req[1]) begin
            grant_id <= 2'd1;
            valid <= 1;
        end else if (req[0]) begin
            grant_id <= 2'd0;
            valid <= 1;
        end else begin
            grant_id <= 2'd0;
            valid <= 0;
        end
    end
end

endmodule
