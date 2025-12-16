class sa_test extends uvm_test;

`uvm_component_utils(sa_test)

sa_env env;
sa_config sa_cfg;
sa_sequence seq;

function new (string name = "sa_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = sa_env::type_id::create("env",this);
    sa_cfg = sa_config::type_id::create("sa_cfg");
    seq = sa_sequence::type_id::create("seq");
    if (!uvm_config_db #(virtual sa_if)::get(this,"","sa_IF",sa_cfg.sa_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the sa from the uvm_config_db");
    sa_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(sa_config)::set(this,"*","CFG",sa_cfg);
    factory.set_type_override_by_type(sa_sequence_item::get_type(),sa_sequence_item_change_constraints::get_type()); // OR
    // factory.set_type_override_by_name("sa_sequence_item","sa_sequence_item_change_constraints");
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    phase.drop_objection(this);
endtask

endclass