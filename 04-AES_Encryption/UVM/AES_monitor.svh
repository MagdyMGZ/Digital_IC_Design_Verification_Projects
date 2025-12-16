class AES_monitor extends uvm_monitor;

`uvm_component_utils(AES_monitor)

virtual AES_if AES_vif;
AES_sequence_item AES_seq_item;
uvm_analysis_port #(AES_sequence_item) mon_ap;

function new (string name = "AES_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        AES_seq_item = AES_sequence_item::type_id::create("AES_seq_item");
        #5;
        AES_seq_item.in  = AES_vif.in;
        AES_seq_item.key = AES_vif.key;
        AES_seq_item.out = AES_vif.out;
        mon_ap.write(AES_seq_item);
        `uvm_info("run_phase",AES_seq_item.convert2string(),UVM_FULL)
    end
endtask

endclass