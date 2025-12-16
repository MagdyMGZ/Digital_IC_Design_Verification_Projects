////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: dB Calculation 10.Log10 Verilog Design
////////////////////////////////////////////////////////////////////////////////
module dB_10log10 #(
    parameter WIDTH = 32        // Q8.24 (8 bits for integer part + 24 bits for fraction part)
) (
    input       wire        [WIDTH-1:0]      log10_in,       // 32 bit Integer Input
    input       wire                         clk,
    input       wire                         rstn,
    input       wire                         enable_in,
    output      wire                         valid_out,
    output      wire        [WIDTH-1:0]      log10_out       // log10_out[31:24] = Integer Part, log10_out[23:0] = Fraction Part
);

// Conversion from log2(x) to 10.log10(x)
// y = 10.log10(x) --> 10^(y/10) = x --> log2(10) * y/10 = log2(x)
// y = 10/log2(10) * log2(x)

localparam conv_log2_to_10log10 = real_to_fixed8_24(3,0103);   // 10/log2(10) = 3.0103

wire               log2_valid;
wire  [WIDTH-1:0]  log2_out;
wire  [WIDTH-1:0]  log2_out_itor;
wire  [63:0]       product;

log2 #(.WIDTH(WIDTH)) log2_instance (
    .log2_in(log10_in),
    .clk(clk),
    .rstn(rstn),
    .enable_in(enable_in),
    .valid_out(log2_valid),
    .log2_out(log2_out)
);

assign log2_out_itor = (log2_valid)? real_to_fixed8_24(log2_out[31:24],log2_out[23:0]) : 0;
assign product       = (log2_valid)? (log2_out_itor * conv_log2_to_10log10) : 0; 
assign log10_out     = (log2_valid)? (product[55:24]) : 0;
assign valid_out     = (log2_valid)? 1 : 0;

// like $itor() function but synthesizable (integer to real)
function [31:0] real_to_fixed8_24;
    input [7:0] integer_part;
    input [23:0] decimal_fraction;
    reg [47:0] temp;
    begin
        // Convert: (decimal_fraction * 2^24) / 10000
        temp = decimal_fraction * 48'd16777216;  // Multiply by 2^24
        temp = temp / 48'd10000;                 // Divide by 10000
        real_to_fixed8_24 = (integer_part << 24) + temp[31:0];
    end
endfunction

endmodule