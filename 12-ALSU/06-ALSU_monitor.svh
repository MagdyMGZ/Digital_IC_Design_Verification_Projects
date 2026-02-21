class ALSU_monitor extends uvm_monitor;
    `uvm_component_utils(ALSU_monitor);
    virtual ALSU_if alsu_vif;
    ALSU_seq_item rsp_seq_item;
    uvm_analysis_port #(ALSU_seq_item) mon_ap;

    function new(string name ="ALSU_monitor",uvm_component parent = null);
        super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);     
        mon_ap=new("mon_ap",this);
    endfunction

    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        forever begin
            rsp_seq_item = ALSU_seq_item::type_id::create("rsp_seq_item");
            @(negedge alsu_vif.clk);
            rsp_seq_item.reset = alsu_vif.reset;
            rsp_seq_item.direction = alsu_vif.direction;
            rsp_seq_item.cin = alsu_vif.cin;
            rsp_seq_item.serial_in = alsu_vif.serial_in;
            rsp_seq_item.bypass_A = alsu_vif.bypass_A;
            rsp_seq_item.bypass_B = alsu_vif.bypass_B;
            rsp_seq_item.red_op_A = alsu_vif.red_op_A;
            rsp_seq_item.red_op_B = alsu_vif.red_op_B;
            rsp_seq_item.A = alsu_vif.A;
            rsp_seq_item.B = alsu_vif.B;
            rsp_seq_item.opcode = alsu_vif.opcode;
            rsp_seq_item.out = alsu_vif.out;
            rsp_seq_item.leds = alsu_vif.leds;
            rsp_seq_item.out_G = alsu_vif.out_G;
            rsp_seq_item.leds_G = alsu_vif.leds_G;
            mon_ap.write(rsp_seq_item);
            `uvm_info("run_phase",rsp_seq_item.convert2string(),UVM_HIGH);
        end
    endtask 

endclass