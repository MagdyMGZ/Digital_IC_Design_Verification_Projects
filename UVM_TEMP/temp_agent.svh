class temp_agent extends uvm_agent;

`uvm_component_utils(temp_agent)

temp_sequencer sqr;
temp_monitor mon;
temp_driver drv;
temp_config temp_cfg;

uvm_analysis_port #(temp_sequence_item) agt_ap;

function new (string name = "temp_agent", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(temp_config)::get(this,"","CFG",temp_cfg))
        `uvm_fatal("build_phase","Unable to get configuration object")
    if (temp_cfg.sel_mode == UVM_ACTIVE) begin
        sqr = temp_sequencer::type_id::create("sqr",this);
        drv = temp_driver::type_id::create("drv",this);
    end
    mon = temp_monitor::type_id::create("mon",this);
    agt_ap = new("agt_ap",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    if (temp_cfg.sel_mode == UVM_ACTIVE) begin
        drv.temp_vif = temp_cfg.temp_vif;
        drv.seq_item_port.connect(sqr.seq_item_export);
    end
    mon.temp_vif = temp_cfg.temp_vif;
    mon.mon_ap.connect(agt_ap);
endfunction

endclass