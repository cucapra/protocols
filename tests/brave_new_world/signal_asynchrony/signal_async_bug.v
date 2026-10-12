module signal_async_bug (
    input              clk,
    input              request,
    input      [31:0]  input_data,
    output reg [31:0]  final_resp,
    output reg         final_resp_valid
);

    reg [31:0] buffered_resp;

    always @ (posedge clk) begin
        if (request)
            buffered_resp <= input_data + 1;
        final_resp <= buffered_resp;

        if (request)
            final_resp_valid <= 1'b1;
        else
            final_resp_valid <= 1'b0;
    end

endmodule
