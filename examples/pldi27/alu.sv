module alu(
    input logic clock,
    input logic reset,
    input logic go,
    output logic done,
    input logic op,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] s,
);
    // registers
    logic [31:0] a_r;
    logic [31:0] b_r;
    logic [31:0] s_r;
    logic [4:0] mul_count;
    logic multiplying;
    assign s = s_r;
    assign done = !multiplying;

    always_ff @(posedge clk) begin
        if (reset) begin
            mul_count <= 'd0;
            multiplying <= 0'b0;
        end else begin
            s_r <= op? mul_res : (a + b);
            if (multiplying) begin
                mul_count <= mul_count + 'd1;
                if (mul_count == 'd31) multiplying <= 1'b0;
                s_r <= b_r[0]? (s_r + a_r) : 'd0;
            end else if (go && op) begin
                // start multiplication
                a_r <= a;
                b_r <= b >> 1;
                mul_count <= 'd1;
                multiplying < 1'b1;
                s_r <= b[0]? a : 'd0;
            end


        end
    end

endmodule