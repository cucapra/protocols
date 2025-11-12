// Taken from Brave New World, bit truncation fft
module bit_truncation_fft_bug (
    input  wire        clk,
    input  wire [26:0] input_data,
    output reg  [10:0] output_data
);

    // 11 bit add. If truncated value is all 1's
    // then the round up overflows and causes wrong result
    wire [10:0] truncated_value = input_data[22:12];
    wire [10:0] rounded_up      = truncated_value + 11'd1;

    wire last_valid_bit     = input_data[12];    
    wire first_lost_bit     = input_data[11];  
    wire [10:0] other_lost_bits;

    assign other_lost_bits = input_data[10:0];

    always @(posedge clk) begin
        if (!first_lost_bit)         
            output_data <= truncated_value;
        else if (|other_lost_bits)   
            output_data <= rounded_up;
        else if (last_valid_bit)       
            output_data <= rounded_up;
        else                         
            output_data <= truncated_value;
    end
endmodule


