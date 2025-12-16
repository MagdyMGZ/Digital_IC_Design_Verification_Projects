import uvm_pkg::*;
`include "uvm_macros.svh"
import sa_pkg::*;

module top ();

sa_if sa_vif ();
simpleadder DUT (sa_vif.clk,sa_vif.en_i,sa_vif.ina,sa_vif.inb,sa_vif.en_o,sa_vif.out);
bind simpleadder sa_sva sva_inst (sa_vif.en_i, sa_vif.ina, sa_vif.inb, sa_vif.clk, sa_vif.out, sa_vif.en_o, DUT.temp_out);

initial begin
    uvm_config_db #(virtual sa_if)::set(null,"uvm_test_top","sa_IF",sa_vif);
    run_test();
end

endmodule