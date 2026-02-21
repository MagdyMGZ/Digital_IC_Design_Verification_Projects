interface ram_if (clk);
input clk;
logic [9:0] din;
logic       rst_n, rx_valid;
logic [7:0] dout;
logic       tx_valid;
logic [7:0] dout_gm;
logic       tx_valid_gm;
endinterface

