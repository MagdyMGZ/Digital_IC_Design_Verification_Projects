class FIFO_test extends uvm_test;

`uvm_component_utils(FIFO_test)

FIFO_env env;
FIFO_config FIFO_cfg;
FIFO_reset_sequence rst_seq;
FIFO_main_sequence main_seq;

function new (string name = "FIFO_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = FIFO_env::type_id::create("env",this);
    FIFO_cfg = FIFO_config::type_id::create("FIFO_cfg");
    rst_seq = FIFO_reset_sequence::type_id::create("rst_seq");
    main_seq = FIFO_main_sequence::type_id::create("main_seq");
    if (!uvm_config_db #(virtual FIFO_if)::get(this,"","FIFO_IF",FIFO_cfg.FIFO_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the FIFO from the uvm_config_db");
    FIFO_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(FIFO_config)::set(this,"*","CFG",FIFO_cfg);
    // factory.set_type_override_by_type(FIFO_sequence_item::get_type(),FIFO_sequence_item_change_constraints::get_type()); // OR
    // factory.set_type_override_by_name("FIFO_sequence_item","FIFO_sequence_item_change_constraints");
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
   
    `uvm_info("run_phase","Reset Asserted",UVM_LOW)
    rst_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Reset Deasserted",UVM_LOW)
    
    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    main_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)
    
    phase.drop_objection(this);
endtask

endclass