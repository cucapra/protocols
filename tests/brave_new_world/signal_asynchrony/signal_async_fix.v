module signal_async_fix (
    input              clk,
    input              request,
    input      [31:0]  input_data,
    output reg [31:0]  final_resp,
    output reg         final_resp_valid
);

    reg [31:0] buffered_resp;
    reg        buffered_resp_valid;

    always @ (posedge clk) begin
        if (request)
            buffered_resp <= input_data + 1;
        final_resp <= buffered_resp;

        if (request)
            buffered_resp_valid <= 1'b1;
        final_resp_valid <= buffered_resp_valid;
    end

endmodule
