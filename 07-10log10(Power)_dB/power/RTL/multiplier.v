////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: Multiplier Verilog Design
////////////////////////////////////////////////////////////////////////////////
module multiplier #(
    parameter IN_WIDTH  = 16
) (
    input       wire    signed      [IN_WIDTH-1:0]      mult_in1,
    input       wire    signed      [IN_WIDTH-1:0]      mult_in2,
    output      wire                [2*IN_WIDTH-1:0]    mult_out
);

assign mult_out = mult_in1 * mult_in2;

endmodule