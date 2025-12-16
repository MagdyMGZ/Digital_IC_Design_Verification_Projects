class ASYNCH_FIFO_collector extends uvm_component;

`uvm_component_utils(ASYNCH_FIFO_collector)

uvm_analysis_port #(ASYNCH_FIFO_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(ASYNCH_FIFO_sequence_item) cov_fifo;

ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;

covergroup ASYNCH_FIFO_cov_grp;
        // Here we create cover point for each signal to be used in the cross coverage
        i_rst_n_cp : coverpoint ASYNCH_FIFO_seq_item.i_rst_n;
        i_wen_cp   : coverpoint ASYNCH_FIFO_seq_item.i_wen;
        i_ren_cp   : coverpoint ASYNCH_FIFO_seq_item.i_ren;
        i_wdata_cp : coverpoint ASYNCH_FIFO_seq_item.i_wdata;
        o_full_cp	 : coverpoint ASYNCH_FIFO_seq_item.o_full;
        o_empty_cp : coverpoint ASYNCH_FIFO_seq_item.o_empty;
        o_rdata_cp : coverpoint ASYNCH_FIFO_seq_item.o_rdata;
        
        // Here we create cross coverage for each output with read enable & write enable
        wr_rd_full_cross : cross i_wen_cp , i_ren_cp , o_full_cp;
        wr_rd_empty_cross : cross i_wen_cp , i_ren_cp , o_empty_cp;
endgroup

function new (string name = "ASYNCH_FIFO_collector", uvm_component parent = null);
    super.new(name,parent);
    ASYNCH_FIFO_cov_grp = new();
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    cov_export = new("cov_export",this);
    cov_fifo = new("cov_fifo",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    cov_export.connect(cov_fifo.analysis_export);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        cov_fifo.get(ASYNCH_FIFO_seq_item);
        ASYNCH_FIFO_cov_grp.sample();
    end
endtask

endclass