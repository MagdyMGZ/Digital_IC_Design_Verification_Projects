package shift_reg_test_pkg;
import shift_reg_env_pkg::*;
import shift_reg_config_pkg::*;
import uvm_pkg::*;
import shift_reg_sequence_pkg::*;
import shift_reg_seq_item_pkg::*;
`include "uvm_macros.svh"
class shift_reg_test extends uvm_test;
  `uvm_component_utils (shift_reg_test)
  shift_reg_env env;
  shift_reg_config shift_reg_cfg;
  shift_reg_main_sequence main_seq;
  shift_reg_reset_sequence reset_seq;
  function new (string name = "shift_reg_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = shift_reg_env::type_id::create("env",this);
    shift_reg_cfg = shift_reg_config::type_id::create("shift_reg_cfg");
    main_seq = shift_reg_main_sequence::type_id::create("main_seq");
    reset_seq = shift_reg_reset_sequence::type_id::create("reset_seq");
    if (!uvm_config_db#(virtual shift_reg_if)::get(this,"","shift_reg_IF",shift_reg_cfg.shift_reg_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the shift_reg from the uvm_config_db")
    shift_reg_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db#(shift_reg_config)::set(this,"*","CFG",shift_reg_cfg);
    factory.set_type_override_by_type(shift_reg_seq_item::get_type(), shift_reg_seq_item_disable_rst::get_type());
  endfunction
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    // reset Sequence
    `uvm_info("run_phase","Reset Asserted",UVM_LOW)
    reset_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Reset Deasserted",UVM_LOW)
    // main Sequence
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    main_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
endpackage


