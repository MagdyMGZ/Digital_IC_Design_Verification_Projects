module WRAPPER_GM (MOSI,MISO,SS_n,clk,rst_n);

input  MOSI, SS_n, clk, rst_n;
output MISO;

wire [9:0] rx_data_din;
wire       rx_valid;
wire       tx_valid;
wire [7:0] tx_data_dout;

RAM_GM   RAM_gm_instance   (rx_data_din,clk,rst_n,rx_valid,tx_data_dout,tx_valid);
SLAVE_GM SLAVE_gm_instance (clk,rst_n,MOSI,SS_n,tx_data_dout,tx_valid,MISO,rx_data_din,rx_valid);

endmodule

