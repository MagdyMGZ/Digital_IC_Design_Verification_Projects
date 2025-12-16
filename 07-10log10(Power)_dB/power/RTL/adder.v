////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: Adder Verilog Design
////////////////////////////////////////////////////////////////////////////////
module adder #(
    parameter IN_WIDTH = 16
) (
    input       wire        [2*IN_WIDTH-1:0]     adder_in1, 
    input       wire        [2*IN_WIDTH-1:0]     adder_in2,
    output      wire        [2*IN_WIDTH-1:0]     adder_out
);

assign adder_out = adder_in1 + adder_in2;

endmodule