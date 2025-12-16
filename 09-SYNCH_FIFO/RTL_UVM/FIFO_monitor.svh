class FIFO_monitor extends uvm_monitor;

`uvm_component_utils(FIFO_monitor)

virtual FIFO_if FIFO_vif;
FIFO_sequence_item FIFO_seq_item;
uvm_analysis_port #(FIFO_sequence_item) mon_ap;

function new (string name = "FIFO_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
        @(FIFO_vif.cb_monitor); // Not // @(posedge FIFO_vif.clk);
        FIFO_seq_item.data_in = FIFO_vif.cb_monitor.data_in;
        FIFO_seq_item.wr_en = FIFO_vif.cb_monitor.wr_en;
        FIFO_seq_item.rd_en = FIFO_vif.cb_monitor.rd_en;
        FIFO_seq_item.rst_n = FIFO_vif.cb_monitor.rst_n;
        FIFO_seq_item.data_out = FIFO_vif.cb_monitor.data_out;
        FIFO_seq_item.full = FIFO_vif.cb_monitor.full;
        FIFO_seq_item.almostfull = FIFO_vif.cb_monitor.almostfull;
        FIFO_seq_item.empty = FIFO_vif.cb_monitor.empty;
        FIFO_seq_item.almostempty = FIFO_vif.cb_monitor.almostempty;
        FIFO_seq_item.overflow = FIFO_vif.cb_monitor.overflow;
        FIFO_seq_item.underflow = FIFO_vif.cb_monitor.underflow;
        FIFO_seq_item.wr_ack = FIFO_vif.cb_monitor.wr_ack;
        mon_ap.write(FIFO_seq_item);
        `uvm_info("run_phase",FIFO_seq_item.convert2string(),UVM_FULL)
    end
endtask

endclass