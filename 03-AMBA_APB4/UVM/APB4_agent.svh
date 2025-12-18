class APB4_agent extends uvm_agent;

`uvm_component_utils(APB4_agent)

APB4_sequencer sqr;
APB4_monitor mon;
APB4_driver drv;
APB4_config APB4_cfg;

uvm_analysis_port #(APB4_sequence_item) agt_ap;

function new (string name = "APB4_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(APB4_config)::get(this,"","CFG",APB4_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (APB4_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = APB4_sequencer::type_id::create("sqr",this);
        drv = APB4_driver::type_id::create("drv",this);
    end
    mon = APB4_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (APB4_cfg.sel_mode == UVM_ACTIVE) begin
        drv.APB4_vif = APB4_cfg.APB4_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.APB4_vif = APB4_cfg.APB4_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass