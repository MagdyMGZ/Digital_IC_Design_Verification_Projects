import wrapper_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module wrapper_top ();
  bit clk;
  
  initial begin
    clk = 0;
    forever
      #1 clk = ~clk;
  end
  
  wrapper_if wrapper_vif (clk);
  ram_if ram_vif (clk);
  slave_if slave_vif (clk);

  WRAPPER DUT_WRAPPER (wrapper_vif.MOSI,wrapper_vif.MISO,wrapper_vif.SS_n,clk,wrapper_vif.rst_n);
  WRAPPER_GM DUT_WRAPPER_GM (wrapper_vif.MOSI,wrapper_vif.MISO_gm,wrapper_vif.SS_n,clk,wrapper_vif.rst_n);

  bind WRAPPER WRAPPER_SVA WRAPPER_SVA_INST (wrapper_vif.MOSI,wrapper_vif.MISO,wrapper_vif.SS_n,clk,wrapper_vif.rst_n);
  
  initial begin
    uvm_config_db#(virtual wrapper_if)::set(null,"uvm_test_top","WRAPPER_IF",wrapper_vif);
    uvm_config_db#(virtual ram_if)::set(null,"uvm_test_top","RAM_IF",ram_vif);
    uvm_config_db#(virtual slave_if)::set(null,"uvm_test_top","SLAVE_IF",slave_vif);
    run_test("wrapper_test");
  end

  initial begin
    $readmemh("RAM.dat",DUT_WRAPPER.RAM_instance.MEM);
    $readmemh("RAM.dat",DUT_WRAPPER_GM.RAM_gm_instance.MEM);
  end

  assign ram_vif.din        = DUT_WRAPPER.rx_data_din;
  assign ram_vif.rst_n      = DUT_WRAPPER.rst_n;
  assign ram_vif.rx_valid   = DUT_WRAPPER.rx_valid;
  assign ram_vif.dout       = DUT_WRAPPER.tx_data_dout;
  assign ram_vif.tx_valid   = DUT_WRAPPER.tx_valid;

  assign ram_vif.dout_gm     = DUT_WRAPPER_GM.tx_data_dout;
  assign ram_vif.tx_valid_gm = DUT_WRAPPER_GM.tx_valid;
  
  assign slave_vif.MOSI     = DUT_WRAPPER.MOSI;
  assign slave_vif.rst_n    = DUT_WRAPPER.rst_n;
  assign slave_vif.SS_n     = DUT_WRAPPER.SS_n;
  assign slave_vif.tx_valid = DUT_WRAPPER.tx_valid;
  assign slave_vif.tx_data  = DUT_WRAPPER.tx_data_dout;
  assign slave_vif.rx_data  = DUT_WRAPPER.rx_data_din;
  assign slave_vif.rx_valid = DUT_WRAPPER.rx_valid;
  assign slave_vif.MISO     = DUT_WRAPPER.MISO;

  assign slave_vif.rx_data_gm  = DUT_WRAPPER_GM.rx_data_din;
  assign slave_vif.rx_valid_gm = DUT_WRAPPER_GM.rx_valid;
  assign slave_vif.MISO_gm     = DUT_WRAPPER_GM.MISO;
  
endmodule

