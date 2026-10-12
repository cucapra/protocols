module fsm_update_fixed_gated (
    input  wire        clk,
    input  wire        reset,        // synchronous reset
    input  wire        start,
    input  wire        finish,
    input  wire        almfull,      // back-pressure
    input  wire        result_valid, // result becomes valid in DO_WORK
    output reg         valid,
    output reg  [31:0] data
);
    localparam [1:0] DO_IDLE   = 2'd0,
                     DO_WORK   = 2'd1,
                     DO_RESULT = 2'd2;

    reg [1:0] state;

    // State register + transitions
    always @(posedge clk) begin
        if (reset) begin
            state <= DO_IDLE;
        end else begin
            case (state)
                DO_IDLE:   if (start)    state <= DO_WORK;
                DO_WORK:   if (finish)   state <= DO_RESULT;
                DO_RESULT: if (!almfull) state <= DO_IDLE;
                default:                 state <= DO_IDLE;
            endcase
        end
    end

    always @(posedge clk) begin
        if (reset) begin
            valid <= 1'b0;
            data  <= 32'd0;
        end else begin
            case (state)
                DO_IDLE: begin
                    valid <= 1'b0;
                end

                DO_WORK: begin
                    if (result_valid && !(finish && almfull)) begin
                        valid <= 1'b1;
                        data  <= 32'hFFFFFFFF; 
                    end else begin
                        valid <= 1'b0;
                    end
                end

                DO_RESULT: begin
                    if (!almfull) begin
                        valid <= 1'b1;
                        data  <= 32'hAAAAAAAA; 
                    end else begin
                        valid <= 1'b0;
                    end
                end

                default: begin
                    valid <= 1'b0;
                end
            endcase
        end
    end
endmodule