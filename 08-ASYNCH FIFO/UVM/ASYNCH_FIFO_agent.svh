class ASYNCH_FIFO_agent extends uvm_agent;

`uvm_component_utils(ASYNCH_FIFO_agent)

ASYNCH_FIFO_sequencer sqr;
ASYNCH_FIFO_monitor mon;
ASYNCH_FIFO_driver drv;
ASYNCH_FIFO_config ASYNCH_FIFO_cfg;

uvm_analysis_port #(ASYNCH_FIFO_sequence_item) agt_ap;

function new (string name = "ASYNCH_FIFO_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(ASYNCH_FIFO_config)::get(this,"","CFG",ASYNCH_FIFO_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (ASYNCH_FIFO_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = ASYNCH_FIFO_sequencer::type_id::create("sqr",this);
        drv = ASYNCH_FIFO_driver::type_id::create("drv",this);
    end
    mon = ASYNCH_FIFO_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (ASYNCH_FIFO_cfg.sel_mode == UVM_ACTIVE) begin
        drv.ASYNCH_FIFO_vif = ASYNCH_FIFO_cfg.ASYNCH_FIFO_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.ASYNCH_FIFO_vif = ASYNCH_FIFO_cfg.ASYNCH_FIFO_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass