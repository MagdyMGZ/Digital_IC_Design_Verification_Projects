class AHB5_monitor extends uvm_monitor;

`uvm_component_utils(AHB5_monitor)

virtual AHB5_BFM_if AHB5_vif;
AHB5_sequence_item AHB5_seq_item;
uvm_analysis_port #(AHB5_sequence_item) mon_ap;
int unsigned transaction_counter_mon;

function new (string name = "AHB5_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    @(posedge AHB5_vif.HRESETn);
    forever begin
        AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
        @(AHB5_vif.cb_monitor);                                 // Not // @(posedge AHB5_vif.PCLK);
        AHB5_seq_item.HRESETn = AHB5_vif.cb_monitor.HRESETn;
        AHB5_seq_item.HSEL1 = AHB5_vif.cb_monitor.HSEL1;
        AHB5_seq_item.HREADY = AHB5_vif.cb_monitor.HREADY;
        AHB5_seq_item.HADDR = AHB5_vif.cb_monitor.HADDR;
        AHB5_seq_item.HBURST = AHB5_vif.cb_monitor.HBURST;
        AHB5_seq_item.HSIZE = AHB5_vif.cb_monitor.HSIZE;
        AHB5_seq_item.HTRANS = AHB5_vif.cb_monitor.HTRANS;
        AHB5_seq_item.HWDATA = AHB5_vif.cb_monitor.HWDATA;
        AHB5_seq_item.HWSTRB = AHB5_vif.cb_monitor.HWSTRB;
        AHB5_seq_item.HWRITE = AHB5_vif.cb_monitor.HWRITE;
        AHB5_seq_item.HRDATA = AHB5_vif.cb_monitor.HRDATA;
        AHB5_seq_item.HREADYOUT = AHB5_vif.cb_monitor.HREADYOUT;
        AHB5_seq_item.HRESP = AHB5_vif.cb_monitor.HRESP;
        mon_ap.write(AHB5_seq_item);
        `uvm_info("run_phase",AHB5_seq_item.convert2string(),UVM_FULL)
        transaction_counter_mon++;
    end
endtask

function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("MONITORED %0d TRANSACTIONS", transaction_counter_mon), UVM_MEDIUM)
endfunction

endclass