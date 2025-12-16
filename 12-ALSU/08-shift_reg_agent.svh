class shift_reg_agent extends uvm_agent;
    `uvm_component_utils(shift_reg_agent);

    shift_reg_config_obj config_obj_driver;
    shift_reg_driver drv;
    shift_reg_sequencer sqr;
    shift_reg_monitor mon;

    uvm_analysis_port #(shift_reg_seq_item) agt_ap;

    function new(string name ="shift_reg_agent",uvm_component parent = null);
        super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(shift_reg_config_obj)::get(this,"","CGO",config_obj_driver)) begin
            `uvm_fatal("build_phase","DRIVER-unable to get the virtual interface");
        end
        if (config_obj_driver.sel_mod == UVM_ACTIVE) begin
            drv = shift_reg_driver::type_id::create("drv",this);
            sqr = shift_reg_sequencer::type_id::create("sqr",this);  
        end
        mon = shift_reg_monitor::type_id::create("mon",this);
        agt_ap = new("agt_ap",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (config_obj_driver.sel_mod == UVM_ACTIVE) begin
            drv.seq_item_port.connect(sqr.seq_item_export);
            drv.shift_reg_vif = config_obj_driver.shift_reg_vif;
        end
        mon.shift_reg_vif = config_obj_driver.shift_reg_vif;
        mon.mon_ap.connect(agt_ap);
    endfunction

endclass