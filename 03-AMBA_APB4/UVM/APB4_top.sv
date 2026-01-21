module top ();
`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"
import APB4_pkg::*;

APB4_BFM_if #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.MEM_DEPTH(MEM_DEPTH)) APB4_vif ();

APB4_BUS_WRAPPER #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.MEM_DEPTH(MEM_DEPTH)) DUT (
    .PCLK(APB4_vif.PCLK),
    .PRESETn(APB4_vif.PRESETn),
    .TRANSFER(APB4_vif.TRANSFER),
    .WRITE(APB4_vif.WRITE),
    .ADDR(APB4_vif.ADDR),
    .WDATA(APB4_vif.WDATA),
    .STRB(APB4_vif.STRB),
    .READY(APB4_vif.READY),
    .RDATA(APB4_vif.RDATA),
    .SLVERR(APB4_vif.SLVERR)
);

bind APB4_BUS_WRAPPER APB4_sva #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.MEM_DEPTH(MEM_DEPTH)) sva_inst (
    .PCLK(DUT.PCLK),
    .PRESETn(DUT.PRESETn),
    .TRANSFER(DUT.TRANSFER),
    .WRITE(DUT.WRITE),
    .ADDR(DUT.ADDR),
    .WDATA(DUT.WDATA),
    .STRB(DUT.STRB),
    .READY(DUT.READY),
    .RDATA(DUT.RDATA),
    .SLVERR(DUT.SLVERR),
    .PSEL0(DUT.PSEL0),  
    .PSEL1(DUT.PSEL1), 
    .PENABLE(DUT.PENABLE)
);

initial begin
    uvm_config_db #(virtual APB4_BFM_if)::set(null,"uvm_test_top","APB4_BFM_IF",APB4_vif);
    run_test();
end

endmodule