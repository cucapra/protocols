module round11_rne_unsigned_fixed (
    input  wire        clk,
    input  wire [26:0] input_data,
    output reg  [10:0] output_data
);
    wire [10:0] truncated_value = input_data[22:12];

    // FIX: perform a 12-bit add to detect overflow
    // and then saturate it
    wire [11:0] round_up            = {1'b0, truncated_value} + 12'd1;
    wire [10:0] rounded_up_sat  = round_up[11] ? 11'h7FF : round_up[10:0];

    wire        last_valid_bit   = input_data[12];   
    wire        first_lost_bit   = input_data[11];     
    wire [10:0] other_lost_bits  = input_data[10:0];  


    always @(posedge clk) begin
        if (!first_lost_bit)            
            output_data <= truncated_value;
        else if (|other_lost_bits)        
            output_data <= rounded_up_sat;
        else if (last_valid_bit)        
            output_data <= rounded_up_sat;
        else                           
            output_data <= truncated_value;
    end
endmodule
