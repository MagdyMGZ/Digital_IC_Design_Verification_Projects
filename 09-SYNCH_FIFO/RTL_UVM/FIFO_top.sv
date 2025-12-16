module top ();

import uvm_pkg::*;
`include "uvm_macros.svh"
import FIFO_pkg::*;


FIFO_if #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) FIFO_vif ();

FIFO #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) DUT (FIFO_vif.clk,FIFO_vif.data_in,FIFO_vif.wr_en,FIFO_vif.rd_en,FIFO_vif.rst_n,
     FIFO_vif.data_out,FIFO_vif.full,FIFO_vif.almostfull,FIFO_vif.empty,FIFO_vif.almostempty,FIFO_vif.overflow,FIFO_vif.underflow,FIFO_vif.wr_ack);

bind FIFO FIFO_sva #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) sva_inst (FIFO_vif.clk,FIFO_vif.data_in,FIFO_vif.wr_en,FIFO_vif.rd_en,FIFO_vif.rst_n,FIFO_vif.data_out,
     FIFO_vif.full,FIFO_vif.almostfull,FIFO_vif.empty,FIFO_vif.almostempty,FIFO_vif.overflow,FIFO_vif.underflow,FIFO_vif.wr_ack,DUT.count,DUT.wr_ptr,DUT.rd_ptr);

initial begin
    uvm_config_db #(virtual FIFO_if)::set(null,"uvm_test_top","FIFO_IF",FIFO_vif);
    run_test();
end

endmodule