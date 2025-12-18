class APB4_monitor extends uvm_monitor;

`uvm_component_utils(APB4_monitor)

virtual APB4_BFM_if APB4_vif;
APB4_sequence_item APB4_seq_item;
uvm_analysis_port #(APB4_sequence_item) mon_ap;
int unsigned transaction_counter_mon;

function new (string name = "APB4_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    @(posedge APB4_vif.PRESETn);
    forever begin
        APB4_seq_item = APB4_sequence_item::type_id::create("APB4_seq_item");
        @(APB4_vif.cb_monitor);                                 // Not // @(posedge APB4_vif.PCLK);
        APB4_seq_item.PRESETn = APB4_vif.cb_monitor.PRESETn;
        APB4_seq_item.TRANSFER = APB4_vif.cb_monitor.TRANSFER;
        APB4_seq_item.WRITE = APB4_vif.cb_monitor.WRITE;
        APB4_seq_item.ADDR = APB4_vif.cb_monitor.ADDR;
        APB4_seq_item.WDATA = APB4_vif.cb_monitor.WDATA;
        APB4_seq_item.STRB = APB4_vif.cb_monitor.STRB;
        APB4_seq_item.READY = APB4_vif.cb_monitor.READY;
        APB4_seq_item.RDATA = APB4_vif.cb_monitor.RDATA;
        APB4_seq_item.SLVERR = APB4_vif.cb_monitor.SLVERR;
        APB4_seq_item.kind = type_e'(APB4_vif.cb_monitor.WRITE);
        APB4_seq_item.slave = slv_sel'(APB4_vif.cb_monitor.ADDR[ADDR_WIDTH-1]);
        mon_ap.write(APB4_seq_item);
        `uvm_info("run_phase",APB4_seq_item.convert2string(),UVM_FULL)
        transaction_counter_mon++;
    end
endtask

function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("MONITORED %0d TRANSACTIONS", transaction_counter_mon), UVM_MEDIUM)
endfunction

endclass