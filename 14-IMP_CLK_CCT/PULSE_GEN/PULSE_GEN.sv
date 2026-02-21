//////////////////////////////////////////////////////////////////
// Author      : Magdy Ahmed Abbas
// File        : PULSE_GEN.sv
// Description : Edge Detector (Positive/Negative/Both)
//////////////////////////////////////////////////////////////////
module PULSE_GEN (
    input       logic       i_clk,
    input       logic       i_rst_n,
    input       logic       i_level_signal,
    output      logic       o_posedge_pls_gen,
    output      logic       o_negedge_pls_gen,
    output      logic       o_both_edge_pls_gen
);

logic receive_signal;
logic delayed_signal;

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        receive_signal <= 0;
        delayed_signal <= 0;
    end
    else begin
        receive_signal <= i_level_signal;
        delayed_signal <= receive_signal;
    end
end

assign o_posedge_pls_gen   = receive_signal & !delayed_signal;
assign o_negedge_pls_gen   = !receive_signal & delayed_signal;
assign o_both_edge_pls_gen =  receive_signal ^ delayed_signal;

endmodule