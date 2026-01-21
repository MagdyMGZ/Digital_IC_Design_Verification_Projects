module Slow_Fast_Pulse_Sync (
    input       wire        i_clk_tx,
    input       wire        i_clk_rx,
    input       wire        i_rst_n,
    input       wire        i_pulse,
    output      wire        o_pulse
);

reg  i_pulse_tx;
wire o_pulse_sync;
reg  o_pulse_rx;

always @(posedge i_clk_tx or negedge i_rst_n) begin
    if (!i_rst_n)
        i_pulse_tx <= 0;
    else
        i_pulse_tx <= i_pulse;
end

Double_FF_Sync #(.WIDTH(1)) (
    .i_data(i_pulse_tx),
    .i_clk(i_clk_rx),
    .i_rst_n(i_rst_n),
    .o_data(o_pulse_sync)
);

always @(posedge i_clk_tx or negedge i_rst_n) begin
    if (!i_rst_n)
        o_pulse_rx <= 0;
    else
        o_pulse_rx <= o_pulse_sync;
end

assign o_pulse = (!o_pulse_rx && o_pulse_sync);

endmodule