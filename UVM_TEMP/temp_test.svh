class temp_test extends uvm_test;

`uvm_component_utils(temp_test)

temp_env env;
temp_config temp_cfg;
temp_sequence temp_seq;

function new (string name = "temp_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = temp_env::type_id::create("env",this);
    temp_cfg = temp_config::type_id::create("temp_cfg");
    temp_seq = temp_sequence::type_id::create("temp_seq");
    if (!uvm_config_db #(virtual temp_if)::get(this,"","temp_IF",temp_cfg.temp_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the temp from the uvm_config_db");
    temp_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(temp_config)::set(this,"*","CFG",temp_cfg);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
   
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    temp_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    
    phase.drop_objection(this);
endtask

function void end_of_elaboration_phase (uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_config_db#(string)::dump(); // Dump Config DB 
    uvm_top.print_topology();       // Prints Entire Testbench Hierarchy 
endfunction

endclass