class AHB5_test extends uvm_test;

`uvm_component_utils(AHB5_test)

AHB5_env env;
AHB5_config AHB5_cfg;
AHB5_sequence AHB5_seq;

function new (string name = "AHB5_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = AHB5_env::type_id::create("env",this);
    AHB5_cfg = AHB5_config::type_id::create("AHB5_cfg");
    AHB5_seq = AHB5_sequence::type_id::create("AHB5_seq");
    if (!uvm_config_db #(virtual AHB5_BFM_if)::get(this,"","AHB5_BFM_IF",AHB5_cfg.AHB5_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the AHB5 from the uvm_config_db");
    AHB5_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(AHB5_config)::set(this,"*","CFG",AHB5_cfg);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
   
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    AHB5_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    
    phase.drop_objection(this);
endtask

function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_config_db#(string)::dump();
    uvm_top.print_topology(); // Prints entire testbench hierarchy 
endfunction

endclass