class APB4_test extends uvm_test;

`uvm_component_utils(APB4_test)

APB4_env env;
APB4_config APB4_cfg;
APB4_sequence APB4_seq;

function new (string name = "APB4_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = APB4_env::type_id::create("env",this);
    APB4_cfg = APB4_config::type_id::create("APB4_cfg");
    APB4_seq = APB4_sequence::type_id::create("APB4_seq");
    if (!uvm_config_db #(virtual APB4_BFM_if)::get(this,"","APB4_BFM_IF",APB4_cfg.APB4_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the APB4 from the uvm_config_db");
    APB4_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(APB4_config)::set(this,"*","CFG",APB4_cfg);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
   
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    APB4_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    
    phase.drop_objection(this);
endtask

function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_config_db#(string)::dump();
    uvm_top.print_topology(); // Prints entire testbench hierarchy 
endfunction

endclass