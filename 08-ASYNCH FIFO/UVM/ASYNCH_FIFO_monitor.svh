class ASYNCH_FIFO_monitor extends uvm_monitor;

`uvm_component_utils(ASYNCH_FIFO_monitor)

virtual ASYNCH_FIFO_if ASYNCH_FIFO_vif;
ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;
uvm_analysis_port #(ASYNCH_FIFO_sequence_item) mon_ap;

function new (string name = "ASYNCH_FIFO_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");

        case ({ASYNCH_FIFO_seq_item.i_ren , ASYNCH_FIFO_seq_item.i_wen})
            2'b01 : begin
                @(ASYNCH_FIFO_vif.cb_monitor_wr);
                ASYNCH_FIFO_seq_item.i_wen = ASYNCH_FIFO_vif.cb_monitor_wr.i_wen;
                ASYNCH_FIFO_seq_item.i_ren = ASYNCH_FIFO_vif.cb_monitor_wr.i_ren;
                ASYNCH_FIFO_seq_item.i_rst_n = ASYNCH_FIFO_vif.cb_monitor_wr.i_rst_n;
                ASYNCH_FIFO_seq_item.i_wdata = ASYNCH_FIFO_vif.cb_monitor_wr.i_wdata;
                ASYNCH_FIFO_seq_item.o_rdata = ASYNCH_FIFO_vif.cb_monitor_wr.o_rdata;
                ASYNCH_FIFO_seq_item.o_full = ASYNCH_FIFO_vif.cb_monitor_wr.o_full;
                ASYNCH_FIFO_seq_item.o_empty = ASYNCH_FIFO_vif.cb_monitor_wr.o_empty;
                ASYNCH_FIFO_seq_item.o_rdata_gold = ASYNCH_FIFO_vif.cb_monitor_wr.o_rdata_gold;
                ASYNCH_FIFO_seq_item.o_full_gold = ASYNCH_FIFO_vif.cb_monitor_wr.o_full_gold;
                ASYNCH_FIFO_seq_item.o_empty_gold = ASYNCH_FIFO_vif.cb_monitor_wr.o_empty_gold;
            end
            2'b10 : begin
                @(ASYNCH_FIFO_vif.cb_monitor_rd);
                ASYNCH_FIFO_seq_item.i_wen = ASYNCH_FIFO_vif.cb_monitor_rd.i_wen;
                ASYNCH_FIFO_seq_item.i_ren = ASYNCH_FIFO_vif.cb_monitor_rd.i_ren;
                ASYNCH_FIFO_seq_item.i_rst_n = ASYNCH_FIFO_vif.cb_monitor_rd.i_rst_n;
                ASYNCH_FIFO_seq_item.i_wdata = ASYNCH_FIFO_vif.cb_monitor_rd.i_wdata;
                ASYNCH_FIFO_seq_item.o_rdata = ASYNCH_FIFO_vif.cb_monitor_rd.o_rdata;
                ASYNCH_FIFO_seq_item.o_full = ASYNCH_FIFO_vif.cb_monitor_rd.o_full;
                ASYNCH_FIFO_seq_item.o_empty = ASYNCH_FIFO_vif.cb_monitor_rd.o_empty;
                ASYNCH_FIFO_seq_item.o_rdata_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_rdata_gold;
                ASYNCH_FIFO_seq_item.o_full_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_full_gold;
                ASYNCH_FIFO_seq_item.o_empty_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_empty_gold;
            end
            default : begin
                @(ASYNCH_FIFO_vif.cb_monitor_wr);
                @(ASYNCH_FIFO_vif.cb_monitor_rd);
                ASYNCH_FIFO_seq_item.i_wen = ASYNCH_FIFO_vif.cb_monitor_rd.i_wen;
                ASYNCH_FIFO_seq_item.i_ren = ASYNCH_FIFO_vif.cb_monitor_rd.i_ren;
                ASYNCH_FIFO_seq_item.i_rst_n = ASYNCH_FIFO_vif.cb_monitor_rd.i_rst_n;
                ASYNCH_FIFO_seq_item.i_wdata = ASYNCH_FIFO_vif.cb_monitor_rd.i_wdata;
                ASYNCH_FIFO_seq_item.o_rdata = ASYNCH_FIFO_vif.cb_monitor_rd.o_rdata;
                ASYNCH_FIFO_seq_item.o_full = ASYNCH_FIFO_vif.cb_monitor_rd.o_full;
                ASYNCH_FIFO_seq_item.o_empty = ASYNCH_FIFO_vif.cb_monitor_rd.o_empty;
                ASYNCH_FIFO_seq_item.o_rdata_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_rdata_gold;
                ASYNCH_FIFO_seq_item.o_full_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_full_gold;
                ASYNCH_FIFO_seq_item.o_empty_gold = ASYNCH_FIFO_vif.cb_monitor_rd.o_empty_gold;
            end
        endcase

        mon_ap.write(ASYNCH_FIFO_seq_item);
        `uvm_info("run_phase",ASYNCH_FIFO_seq_item.convert2string(),UVM_FULL)
    end
endtask

endclass