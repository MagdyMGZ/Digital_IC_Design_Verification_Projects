module WRAPPER_SVA (MOSI,MISO,SS_n,clk,rst_n);

input bit MOSI, clk, rst_n, SS_n;
input bit MISO;

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

// 1- An assertion ensures that whenever reset is asserted, the outputs (MISO) are all inactive.
property rstn_property;
    @(posedge clk) !rst_n |=> (!MISO);
endproperty

// 2- An assertion to make sure that the MISO remains with a stable value as long as it is not a read data operation
property miso_property;
    @(posedge clk) disable iff(!rst_n) write_add_seq or write_data_seq or read_add_seq |=> $stable(MISO) [->1];
endproperty

rstn_assertion: assert property (rstn_property);
rstn_cover:     cover  property (rstn_property);

miso_assertion: assert property (miso_property);
miso_cover:     cover  property (miso_property);

endmodule

