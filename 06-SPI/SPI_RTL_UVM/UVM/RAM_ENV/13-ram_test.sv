package ram_test_pkg;
import ram_config_pkg::*;
import ram_env_pkg::*;
import ram_sequence_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
class ram_test extends uvm_test;
  `uvm_component_utils (ram_test)
  ram_env env_ram;
  ram_config ram_cfg;
  reset_sequence reset_seq;
  write_sequence write_seq;
  read_sequence read_seq;
  write_read_sequence write_read_seq;

  function new (string name = "ram_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env_ram = ram_env::type_id::create("env_ram",this);
    ram_cfg = ram_config::type_id::create("ram_cfg");
    reset_seq = reset_sequence::type_id::create("reset_seq");
    write_seq = write_sequence::type_id::create("write_seq");
    read_seq = read_sequence::type_id::create("read_seq");
    write_read_seq = write_read_sequence::type_id::create("write_read_seq");

    if (!uvm_config_db#(virtual ram_if)::get(this,"","RAM_IF",ram_cfg.ram_vif))
      `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the ram from the uvm_config_db")

    ram_cfg.ram_mode = UVM_ACTIVE;

    uvm_config_db#(ram_config)::set(this,"*","CFG_RAM",ram_cfg);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    `uvm_info("run_phase","Reset Asserted",UVM_LOW)
    reset_seq.start(env_ram.agt.sqr);
    `uvm_info("run_phase","Reset Deasserted",UVM_LOW)

    `uvm_info("run_phase","RAM Write Stimulus Generation Started",UVM_LOW)
    write_seq.start(env_ram.agt.sqr);
    `uvm_info("run_phase","RAM Write Stimulus Generation Ended",UVM_LOW)

    `uvm_info("run_phase","RAM Read Stimulus Generation Started",UVM_LOW)
    read_seq.start(env_ram.agt.sqr);
    `uvm_info("run_phase","RAM Read Stimulus Generation Ended",UVM_LOW)

    `uvm_info("run_phase","RAM Write & Read Stimulus Generation Started",UVM_LOW)
    write_read_seq.start(env_ram.agt.sqr);
    `uvm_info("run_phase","RAM Write & Read Stimulus Generation Ended",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

endpackage

