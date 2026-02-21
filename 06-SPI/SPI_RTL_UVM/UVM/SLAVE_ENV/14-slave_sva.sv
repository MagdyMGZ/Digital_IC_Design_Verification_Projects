module SLAVE_SVA (MOSI,MISO,SS_n,clk,rst_n,rx_data,rx_valid,tx_data,tx_valid);

input bit       MOSI, clk, rst_n, SS_n, tx_valid;
input bit [7:0] tx_data;
input bit [9:0] rx_data;
input bit       rx_valid, MISO;

sequence write_add_seq;
    (!SS_n ##1 !MOSI ##1 !MOSI ##1 !MOSI);
endsequence

sequence write_data_seq;
    (!SS_n ##1 !MOSI ##1 !MOSI ##1 MOSI);
endsequence

sequence read_add_seq;
    (!SS_n ##1 MOSI ##1 MOSI ##1 !MOSI);
endsequence

sequence read_data_seq;
    (!SS_n ##1 MOSI ##1 MOSI ##1 MOSI);
endsequence

// 1- An assertion ensures that whenever reset is asserted, the outputs (MISO, rx_valid, and rx_data) are all low.
property rstn_property;
    @(posedge clk) !rst_n |=> (!MISO && !rx_valid && ~rx_data);
endproperty

// 2- An assertion checks that after any valid command sequence (write_add_seq (000), write_data_seq (001), read_add_seq(110), or read_data_seq(111)), 
//    the rx_valid signal must assert exactly after 10 cycles and the SS_n should eventually after the 10 cycles to close communication.
property tx_valid_property;
    @(posedge clk) disable iff(!rst_n) (!SS_n && tx_valid) |=> $fell(tx_valid) [->1];
endproperty

property rx_valid_property;
    @(posedge clk) disable iff(!rst_n) (write_add_seq or write_data_seq or read_add_seq or read_data_seq) |-> ##10 (rx_valid && $rose(SS_n) [->1]);
endproperty

rstn_assertion: assert property (rstn_property);
rstn_cover:     cover  property (rstn_property);

tx_valid_assertion: assert property (tx_valid_property);
tx_valid_cover:     cover  property (tx_valid_property);

rx_valid_assertion: assert property (rx_valid_property);
rx_valid_cover:     cover  property (rx_valid_property);

endmodule

