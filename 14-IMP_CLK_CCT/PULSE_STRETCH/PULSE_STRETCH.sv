//////////////////////////////////////////////////////////////////
// Author      : Magdy Ahmed Abbas
// File        : PULSE_STRETCH.sv
// Description : Pulse Stretcher 
//////////////////////////////////////////////////////////////////
module PULSE_STRETCH #(
    parameter STRETCH_RATIO = 4
) (
    input       logic       i_clk,
    input       logic       i_rst_n,
    input       logic       i_pulse, 
    output      logic       o_pulse_stretched
);

integer counter;

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) 
        o_pulse_stretched <= 0;
    else if (i_pulse)
        o_pulse_stretched <= 1;
    else if (counter == STRETCH_RATIO-1)
        o_pulse_stretched <= 0;
end

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        counter <= 0;
    end
    else begin
        if (o_pulse_stretched) begin
            counter <= counter + 1;
        end
        else begin
            counter <= 0;
        end
    end
end
    
endmodule