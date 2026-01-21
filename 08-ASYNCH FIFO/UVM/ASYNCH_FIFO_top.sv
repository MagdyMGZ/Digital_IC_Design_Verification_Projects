module top ();

import uvm_pkg::*;
`include "uvm_macros.svh"
import ASYNCH_FIFO_pkg::*;

ASYNCH_FIFO_if #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) ASYNCH_FIFO_vif ();

ASYNCH_FIFO #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) DUT (ASYNCH_FIFO_vif.i_rst_n,ASYNCH_FIFO_vif.i_wclk,ASYNCH_FIFO_vif.i_wen,ASYNCH_FIFO_vif.i_wdata,ASYNCH_FIFO_vif.i_rclk,ASYNCH_FIFO_vif.i_ren,ASYNCH_FIFO_vif.o_full,ASYNCH_FIFO_vif.o_empty,ASYNCH_FIFO_vif.o_rdata);

async_fifo #(.DATA_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) DUT_GOLD (ASYNCH_FIFO_vif.i_rst_n,ASYNCH_FIFO_vif.i_wclk,ASYNCH_FIFO_vif.i_wen,ASYNCH_FIFO_vif.i_wdata,ASYNCH_FIFO_vif.i_rclk,ASYNCH_FIFO_vif.i_ren,ASYNCH_FIFO_vif.o_full_gold,ASYNCH_FIFO_vif.o_empty_gold,ASYNCH_FIFO_vif.o_rdata_gold);

bind ASYNCH_FIFO ASYNCH_FIFO_sva #(.FIFO_WIDTH(FIFO_WIDTH),.FIFO_DEPTH(FIFO_DEPTH)) sva_inst (ASYNCH_FIFO_vif.i_rst_n,ASYNCH_FIFO_vif.i_wclk,ASYNCH_FIFO_vif.i_wen,ASYNCH_FIFO_vif.i_wdata,ASYNCH_FIFO_vif.i_rclk,ASYNCH_FIFO_vif.i_ren,ASYNCH_FIFO_vif.o_full,ASYNCH_FIFO_vif.o_empty,ASYNCH_FIFO_vif.o_rdata,DUT.wr_ptr,DUT.rd_ptr);

initial begin
    uvm_config_db #(virtual ASYNCH_FIFO_if)::set(null,"uvm_test_top","ASYNCH_FIFO_IF",ASYNCH_FIFO_vif);
    run_test();
end

initial begin
    $readmemb("mem.dat",DUT.MEM);
end

endmodule