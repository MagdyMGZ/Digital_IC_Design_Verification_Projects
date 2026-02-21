class temp_monitor extends uvm_monitor;

`uvm_component_utils(temp_monitor)

virtual temp_if temp_vif;
temp_sequence_item temp_seq_item;
uvm_analysis_port #(temp_sequence_item) mon_ap;

int unsigned transaction_counter_mon;

function new (string name = "temp_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        temp_seq_item = temp_sequence_item::type_id::create("temp_seq_item");
        
        // Blocking Event
        
        mon_ap.write(temp_seq_item);
        `uvm_info("run_phase",temp_seq_item.convert2string(),UVM_FULL)
        transaction_counter_mon++;
    end
endtask

function void report_phase (uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("report_phase", $sformatf("MONITORED %0d TRANSACTIONS", transaction_counter_mon), UVM_MEDIUM)
endfunction

endclass