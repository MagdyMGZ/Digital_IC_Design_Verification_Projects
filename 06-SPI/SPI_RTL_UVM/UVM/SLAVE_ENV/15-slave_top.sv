import slave_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module slave_top ();
  bit clk;
  
  initial begin
    clk = 0;
    forever
      #1 clk = ~clk;
  end
  
  slave_if slave_vif (clk);

  SLAVE DUT_SLAVE (slave_vif.MOSI,slave_vif.MISO,slave_vif.SS_n,clk,slave_vif.rst_n,slave_vif.rx_data,slave_vif.rx_valid,slave_vif.tx_data,slave_vif.tx_valid);
  SLAVE_GM DUT_SLAVE_GM (clk,slave_vif.rst_n,slave_vif.MOSI,slave_vif.SS_n,slave_vif.tx_data,slave_vif.tx_valid,slave_vif.MISO_gm,slave_vif.rx_data_gm,slave_vif.rx_valid_gm);

  bind SLAVE SLAVE_SVA SLAVE_SVA_INST (slave_vif.MOSI,slave_vif.MISO,slave_vif.SS_n,clk,slave_vif.rst_n,slave_vif.rx_data,slave_vif.rx_valid,slave_vif.tx_data,slave_vif.tx_valid);
  
  initial begin
    uvm_config_db#(virtual slave_if)::set(null,"uvm_test_top","SLAVE_IF",slave_vif);
    run_test("slave_test");
  end
endmodule

