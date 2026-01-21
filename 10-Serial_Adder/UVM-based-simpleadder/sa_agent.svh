class sa_agent extends uvm_agent;

`uvm_component_utils(sa_agent)

sa_sequencer sqr;
sa_monitor mon;
sa_driver drv;
sa_config sa_cfg;

uvm_analysis_port #(sa_sequence_item) agt_ap;

function new (string name = "sa_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(sa_config)::get(this,"","CFG",sa_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (sa_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = sa_sequencer::type_id::create("sqr",this);
        drv = sa_driver::type_id::create("drv",this);
    end
    mon = sa_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (sa_cfg.sel_mode == UVM_ACTIVE) begin
        drv.sa_vif = sa_cfg.sa_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.sa_vif = sa_cfg.sa_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass