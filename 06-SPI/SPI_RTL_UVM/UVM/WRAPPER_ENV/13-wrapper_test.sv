package wrapper_test_pkg;
import ram_config_pkg::*;
import slave_config_pkg::*;
import wrapper_config_pkg::*;
import ram_env_pkg::*;
import slave_env_pkg::*;
import wrapper_env_pkg::*;
import wrapper_sequence_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
class wrapper_test extends uvm_test;
  `uvm_component_utils (wrapper_test)
  wrapper_env env_wrapper;
  ram_env env_ram;
  slave_env env_slave;
  wrapper_config wrapper_cfg;
  ram_config ram_cfg;
  slave_config slave_cfg;
  reset_sequence reset_seq;
  write_sequence write_seq;
  read_sequence read_seq;
  write_read_sequence write_read_seq;

  function new (string name = "wrapper_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env_wrapper = wrapper_env::type_id::create("env_wrapper",this);
    env_ram = ram_env::type_id::create("env_ram",this);
    env_slave = slave_env::type_id::create("env_slave",this);
    wrapper_cfg = wrapper_config::type_id::create("wrapper_cfg");
    ram_cfg = ram_config::type_id::create("ram_cfg");
    slave_cfg = slave_config::type_id::create("slave_cfg");
    reset_seq = reset_sequence::type_id::create("reset_seq");
    write_seq = write_sequence::type_id::create("write_seq");
    read_seq = read_sequence::type_id::create("read_seq");
    write_read_seq = write_read_sequence::type_id::create("write_read_seq");

    if (!uvm_config_db#(virtual wrapper_if)::get(this,"","WRAPPER_IF",wrapper_cfg.wrapper_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the wrapper from the uvm_config_db")
    if (!uvm_config_db#(virtual ram_if)::get(this,"","RAM_IF",ram_cfg.ram_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the ram from the uvm_config_db")
    if (!uvm_config_db#(virtual slave_if)::get(this,"","SLAVE_IF",slave_cfg.slave_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the slave from the uvm_config_db")
    
    wrapper_cfg.wrapper_mode = UVM_ACTIVE;
    ram_cfg.ram_mode = UVM_PASSIVE;
    slave_cfg.slave_mode = UVM_PASSIVE;

    uvm_config_db#(wrapper_config)::set(this,"env_wrapper.*","CFG_WRAPPER",wrapper_cfg);
    uvm_config_db#(ram_config)::set(this,"env_ram.*","CFG_RAM",ram_cfg);
    uvm_config_db#(slave_config)::set(this,"env_slave.*","CFG_SLAVE",slave_cfg);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    `uvm_info("run_phase","Reset Asserted",UVM_LOW)
    reset_seq.start(env_wrapper.agt.sqr);
    `uvm_info("run_phase","Reset Deasserted",UVM_LOW)

    `uvm_info("run_phase","wrapper Write Stimulus Generation Started",UVM_LOW)
    write_seq.start(env_wrapper.agt.sqr);
    `uvm_info("run_phase","wrapper Write Stimulus Generation Ended",UVM_LOW)

    `uvm_info("run_phase","wrapper Read Stimulus Generation Started",UVM_LOW)
    read_seq.start(env_wrapper.agt.sqr);
    `uvm_info("run_phase","wrapper Read Stimulus Generation Ended",UVM_LOW)

    `uvm_info("run_phase","wrapper Write & Read Stimulus Generation Started",UVM_LOW)
    write_read_seq.start(env_wrapper.agt.sqr);
    `uvm_info("run_phase","wrapper Write & Read Stimulus Generation Ended",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

endpackage