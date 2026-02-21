package slave_test_pkg;
import slave_config_pkg::*;
import slave_env_pkg::*;
import slave_sequence_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
class slave_test extends uvm_test;
  `uvm_component_utils (slave_test)
  slave_env env_slave;
  slave_config slave_cfg;
  reset_sequence reset_seq;
  main_sequence main_seq;

  function new (string name = "slave_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env_slave = slave_env::type_id::create("env_slave",this);
    slave_cfg = slave_config::type_id::create("slave_cfg");
    reset_seq = reset_sequence::type_id::create("reset_seq");
    main_seq = main_sequence::type_id::create("main_seq");

    if (!uvm_config_db#(virtual slave_if)::get(this,"","SLAVE_IF",slave_cfg.slave_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the slave from the uvm_config_db")

    slave_cfg.slave_mode = UVM_ACTIVE;

    uvm_config_db#(slave_config)::set(this,"*","CFG_SLAVE",slave_cfg);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    `uvm_info("run_phase","Reset Asserted",UVM_LOW)
    reset_seq.start(env_slave.agt.sqr);
    `uvm_info("run_phase","Reset Deasserted",UVM_LOW)

    `uvm_info("run_phase","Slave Main Stimulus Generation Started",UVM_LOW)
    main_seq.start(env_slave.agt.sqr);
    `uvm_info("run_phase","Slave Main Stimulus Generation Ended",UVM_LOW)

    phase.drop_objection(this);
  endtask
endclass

endpackage

