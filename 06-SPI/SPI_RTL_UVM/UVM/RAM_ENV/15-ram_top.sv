import ram_test_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

module ram_top ();
  bit clk;
  
  initial begin
    clk = 0;
    forever
      #1 clk = ~clk;
  end
  
  ram_if ram_vif (clk);

  RAM DUT_RAM (ram_vif.din,clk,ram_vif.rst_n,ram_vif.rx_valid,ram_vif.dout,ram_vif.tx_valid);
  RAM_GM DUT_RAM_GM (ram_vif.din,clk,ram_vif.rst_n,ram_vif.rx_valid,ram_vif.dout_gm,ram_vif.tx_valid_gm);

  bind RAM RAM_SVA RAM_SVA_INST (ram_vif.din,clk,ram_vif.rst_n,ram_vif.rx_valid,ram_vif.dout,ram_vif.tx_valid);

  initial begin
    uvm_config_db#(virtual ram_if)::set(null,"uvm_test_top","RAM_IF",ram_vif);
    run_test("ram_test");
  end

  initial begin
    $readmemh ("RAM.dat",DUT_RAM.MEM);
  end
endmodule

