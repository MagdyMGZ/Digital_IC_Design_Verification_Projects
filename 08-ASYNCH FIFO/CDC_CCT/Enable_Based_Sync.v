module Enable_Based_Sync #(
    parameter WIDTH = 4
) (
    input       wire                            i_clk_tx,
    input       wire                            i_clk_rx,
    input       wire                            i_rst_n,
    input       wire                            i_enable,
    input       wire        [WIDTH-1:0]         i_data,
    output      wire        [WIDTH-1:0]         o_data
);

reg [WIDTH-1:0] i_data_tx;
reg             i_en_tx;

reg [WIDTH-1:0] o_data_rx;
wire            o_en_rx;

always @(posedge i_clk_tx or negedge i_rst_n) begin
    if (!i_rst_n) begin
        i_data_tx <= 0;
        i_en_tx <= 0;
    end
    else begin
        i_data_tx <= i_data;
        i_en_tx <= i_enable;
    end
end

Double_FF_Sync #(.WIDTH(1)) (
    .i_data(i_en_tx),
    .i_clk(i_clk_rx),
    .i_rst_n(i_rst_n),
    .o_data(o_en_rx)
);

always @(posedge i_clk_rx or negedge i_rst_n) begin
    if (!i_rst_n)
        o_data_rx <= 0;
    else if (o_en_rx)
        o_data_rx <= i_data_tx;
    else
        o_data_rx <= o_data_rx;
end

assign o_data = o_data_rx;

endmodule