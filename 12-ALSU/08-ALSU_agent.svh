class ALSU_agent extends uvm_agent;
    `uvm_component_utils(ALSU_agent);

    ALSU_config_obj config_obj_driver;
    ALSU_driver drv;
    ALSU_sequencer sqr;
    ALSU_monitor mon;

    uvm_analysis_port #(ALSU_seq_item) agt_ap;

    function new(string name ="ALSU_agent",uvm_component parent = null);
        super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(ALSU_config_obj)::get(this,"","CGO",config_obj_driver)) begin
            `uvm_fatal("build_phase","DRIVER-unable to get the virtual interface");
        end
        if (config_obj_driver.sel_mod == UVM_ACTIVE) begin
            drv = ALSU_driver::type_id::create("drv",this);
            sqr = ALSU_sequencer::type_id::create("sqr",this);  
        end
        mon = ALSU_monitor::type_id::create("mon",this);
        agt_ap = new("agt_ap",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (config_obj_driver.sel_mod == UVM_ACTIVE) begin
            drv.seq_item_port.connect(sqr.seq_item_export);
            drv.alsu_vif = config_obj_driver.alsu_vif;
        end
        mon.alsu_vif = config_obj_driver.alsu_vif;
        mon.mon_ap.connect(agt_ap);
    endfunction

endclass