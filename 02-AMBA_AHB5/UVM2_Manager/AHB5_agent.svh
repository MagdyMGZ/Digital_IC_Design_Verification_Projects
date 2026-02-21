class AHB5_agent extends uvm_agent;

`uvm_component_utils(AHB5_agent)

AHB5_sequencer sqr;
AHB5_monitor mon;
AHB5_driver drv;
AHB5_config AHB5_cfg;

uvm_analysis_port #(AHB5_sequence_item) agt_ap;

function new (string name = "AHB5_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(AHB5_config)::get(this,"","CFG",AHB5_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (AHB5_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = AHB5_sequencer::type_id::create("sqr",this);
        drv = AHB5_driver::type_id::create("drv",this);
    end
    mon = AHB5_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (AHB5_cfg.sel_mode == UVM_ACTIVE) begin
        drv.AHB5_vif = AHB5_cfg.AHB5_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.AHB5_vif = AHB5_cfg.AHB5_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass