//////////////////////////////////////////////////////////////////
// Author      : Magdy Ahmed Abbas
// File        : CLK_GATE.sv
// Description : Clock Gating
//////////////////////////////////////////////////////////////////
module CLK_GATE (
    input       logic       i_clk,
    input       logic       i_clk_en,
    output      logic       o_clk_gated
);

logic latch_en;

always @(i_clk or i_clk_en) begin
    if (!i_clk) begin
        latch_en = i_clk_en;
    end
end

assign o_clk_gated = i_clk & latch_en;
    
endmodule