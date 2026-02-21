module top ();

import uvm_pkg::*;
`include "uvm_macros.svh"

import temp_pkg::*;

import temp_shared_pkg::*;

temp_if #() temp_vif ();

temp_design #() DUT ();

`ifdef ASSERT_ON
    bind temp_design temp_sva #() sva_inst ();
`endif

initial begin
    uvm_config_db #(virtual temp_if)::set(null,"uvm_test_top","temp_IF",temp_vif);
    run_test("temp_test");
end

endmodule