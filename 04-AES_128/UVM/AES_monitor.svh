class AES_monitor extends uvm_monitor;

`uvm_component_utils(AES_monitor)

virtual AES_if AES_vif;
AES_sequence_item AES_seq_item, AES_seq_item_copy;
uvm_analysis_port #(AES_sequence_item) mon_ap;

int unsigned transaction_counter_mon;

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
        AES_seq_item_copy = AES_sequence_item::type_id::create("AES_seq_item_copy");
        #5;
        AES_seq_item.in  = AES_vif.in;
        AES_seq_item.key = AES_vif.key;
        AES_seq_item.out = AES_vif.out;
        AES_seq_item_copy.copy(AES_seq_item);
        mon_ap.write(AES_seq_item_copy);
        `uvm_info("run_phase",AES_seq_item_copy.convert2string(),UVM_FULL)
        `uvm_info(get_type_name(), $sformatf("MONITORED %s: \n%s", AES_seq_item_copy.get_type_name(), AES_seq_item_copy.sprint()), UVM_FULL)
        transaction_counter_mon++;
    end
endtask

virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("MONITORED %0d TRANSACTIONS", transaction_counter_mon), UVM_MEDIUM)
endfunction

endclass