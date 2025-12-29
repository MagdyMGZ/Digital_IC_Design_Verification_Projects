module top ();
import uvm_pkg::*;
`include "uvm_macros.svh"
import AHB5_pkg::*;
import shared_pkg::*;

AHB5_BFM_if AHB5_vif ();

AHB5_Slave_Memory #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.HBURST_WIDTH(HBURST_WIDTH),.MEM_DEPTH(MEM_DEPTH)) DUT (
    .HCLK(AHB5_vif.HCLK),
    .HRESETn(AHB5_vif.HRESETn),
    .HSEL1(AHB5_vif.HSEL1),
    .HREADY(AHB5_vif.HREADY),
    .HADDR(AHB5_vif.HADDR),
    .HBURST(AHB5_vif.HBURST),
    .HSIZE(AHB5_vif.HSIZE),
    .HTRANS(AHB5_vif.HTRANS),
    .HWDATA(AHB5_vif.HWDATA),
    .HWSTRB(AHB5_vif.HWSTRB),
    .HWRITE(AHB5_vif.HWRITE),
    .HRDATA(AHB5_vif.HRDATA),
    .HREADYOUT(AHB5_vif.HREADYOUT),
    .HRESP(AHB5_vif.HRESP)
);

bind AHB5_Slave_Memory AHB5_sva #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.HBURST_WIDTH(HBURST_WIDTH),.MEM_DEPTH(MEM_DEPTH)) sva_inst (
    .HCLK(AHB5_vif.HCLK),
    .HRESETn(AHB5_vif.HRESETn),
    .HSEL1(AHB5_vif.HSEL1),
    .HREADY(AHB5_vif.HREADY),
    .HADDR(AHB5_vif.HADDR),
    .HBURST(AHB5_vif.HBURST),
    .HSIZE(AHB5_vif.HSIZE),
    .HTRANS(AHB5_vif.HTRANS),
    .HWDATA(AHB5_vif.HWDATA),
    .HWSTRB(AHB5_vif.HWSTRB),
    .HWRITE(AHB5_vif.HWRITE),
    .HRDATA(AHB5_vif.HRDATA),
    .HREADYOUT(AHB5_vif.HREADYOUT),
    .HRESP(AHB5_vif.HRESP)
);

initial begin
    uvm_config_db #(virtual AHB5_BFM_if)::set(null,"uvm_test_top","AHB5_BFM_IF",AHB5_vif);
    run_test();
end

endmodule