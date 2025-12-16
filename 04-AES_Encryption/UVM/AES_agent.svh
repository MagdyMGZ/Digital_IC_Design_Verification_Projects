class AES_agent extends uvm_agent;

`uvm_component_utils(AES_agent)

AES_sequencer sqr;
AES_monitor mon;
AES_driver drv;
AES_config AES_cfg;

uvm_analysis_port #(AES_sequence_item) agt_ap;

function new (string name = "AES_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(AES_config)::get(this,"","CFG",AES_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (AES_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = AES_sequencer::type_id::create("sqr",this);
        drv = AES_driver::type_id::create("drv",this);
    end
    mon = AES_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (AES_cfg.sel_mode == UVM_ACTIVE) begin
        drv.AES_vif = AES_cfg.AES_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.AES_vif = AES_cfg.AES_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass