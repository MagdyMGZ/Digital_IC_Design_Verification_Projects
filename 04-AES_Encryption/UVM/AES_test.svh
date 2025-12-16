class AES_test extends uvm_test;

`uvm_component_utils(AES_test)

AES_env env;
AES_config AES_cfg;
AES_sequence AES_seq;

function new (string name = "AES_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = AES_env::type_id::create("env",this);
    AES_cfg = AES_config::type_id::create("AES_cfg");
    AES_seq = AES_sequence::type_id::create("AES_seq");
    if (!uvm_config_db #(virtual AES_if)::get(this,"","AES_IF",AES_cfg.AES_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the AES from the uvm_config_db");
    AES_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(AES_config)::set(this,"*","CFG",AES_cfg);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    AES_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    
    phase.drop_objection(this);
endtask

endclass