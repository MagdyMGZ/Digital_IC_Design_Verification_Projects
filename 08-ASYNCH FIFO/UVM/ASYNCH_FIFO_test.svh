class ASYNCH_FIFO_test extends uvm_test;

`uvm_component_utils(ASYNCH_FIFO_test)

ASYNCH_FIFO_env env;
ASYNCH_FIFO_config ASYNCH_FIFO_cfg;
ASYNCH_FIFO_reset_sequence rst_seq;
ASYNCH_FIFO_main_sequence main_seq;

function new (string name = "ASYNCH_FIFO_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = ASYNCH_FIFO_env::type_id::create("env",this);
    ASYNCH_FIFO_cfg = ASYNCH_FIFO_config::type_id::create("ASYNCH_FIFO_cfg");
    rst_seq = ASYNCH_FIFO_reset_sequence::type_id::create("rst_seq");
    main_seq = ASYNCH_FIFO_main_sequence::type_id::create("main_seq");
    if (!uvm_config_db #(virtual ASYNCH_FIFO_if)::get(this,"","ASYNCH_FIFO_IF",ASYNCH_FIFO_cfg.ASYNCH_FIFO_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the ASYNCH_FIFO from the uvm_config_db");
    ASYNCH_FIFO_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(ASYNCH_FIFO_config)::set(this,"env.agt","CFG",ASYNCH_FIFO_cfg);
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