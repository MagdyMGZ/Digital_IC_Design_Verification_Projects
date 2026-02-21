module Fast_Slow_Pulse_Sync (
    input       wire        i_clk_tx,
    input       wire        i_clk_rx,
    input       wire        i_rst_n,
    input       wire        i_pulse,
    output      wire        o_pulse
);

reg  req;
wire request;
wire req_sync;

wire ack;
wire ack_sync;

reg  o_pulse_reg;

Double_FF_Sync #(.WIDTH(1)) (
    .i_data(req),
    .i_clk(i_clk_tx),
    .i_rst_n(i_rst_n),
    .o_data(req_sync)
);

Double_FF_Sync #(.WIDTH(1)) (
    .i_data(ack),
    .i_clk(i_clk_rx),
    .i_rst_n(i_rst_n),
    .o_data(ack_sync)
);

assign request = (i_pulse)? 1 : (ack_sync)? 0 : req;
assign ack = o_pulse_reg;
assign o_pulse = (!o_pulse_reg && req_sync);

always @(posedge i_clk_tx or negedge i_rst_n) begin
    if (!i_rst_n)
        req <= 0;
    else
        req <= request;
end

always @(posedge i_clk_rx or negedge i_rst_n) begin
    if (!i_rst_n) 
        o_pulse_reg <= 0;
    else
        o_pulse_reg <= req_sync;
end
    
endmodule