class FIFO_collector extends uvm_component;

`uvm_component_utils(FIFO_collector)

uvm_analysis_port #(FIFO_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(FIFO_sequence_item) cov_fifo;

FIFO_sequence_item FIFO_seq_item;

covergroup FIFO_cov_grp;
        // Here we create cover point for each signal to be used in the cross coverage
        wr_en_cp       : coverpoint FIFO_seq_item.wr_en;
        rd_en_cp       : coverpoint FIFO_seq_item.rd_en;
        wr_ack_cp      : coverpoint FIFO_seq_item.wr_ack;
        full_cp	       : coverpoint FIFO_seq_item.full;
        empty_cp       : coverpoint FIFO_seq_item.empty;
        almostfull_cp  : coverpoint FIFO_seq_item.almostfull;
        almostempty_cp : coverpoint FIFO_seq_item.almostempty;
        overflow_cp    : coverpoint FIFO_seq_item.overflow;
        underflow_cp   : coverpoint FIFO_seq_item.underflow;
        
        // Here we create cross coverage for each output with read enable & write enable except(dout)
        wr_rd_wr_ack_cross : cross wr_en_cp , rd_en_cp , wr_ack_cp
                { ignore_bins write_read_01_with_wr_ack = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {1} && binsof(wr_ack_cp) intersect {1};
                  ignore_bins write_read_00_with_wr_ack = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {0} && binsof(wr_ack_cp) intersect {1};}

        wr_rd_full_cross : cross wr_en_cp , rd_en_cp , full_cp 
                { ignore_bins write_read_11_with_full = binsof(wr_en_cp) intersect {1} && binsof(rd_en_cp) intersect {1} && binsof(full_cp) intersect {1};
                  ignore_bins write_read_01_with_full = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {1} && binsof(full_cp) intersect {1};}

        wr_rd_empty_cross : cross wr_en_cp , rd_en_cp , empty_cp
                { ignore_bins write_read_11_with_empty = binsof(wr_en_cp) intersect {1} && binsof(rd_en_cp) intersect {1} && binsof(empty_cp) intersect {1};
                  ignore_bins write_read_10_with_empty = binsof(wr_en_cp) intersect {1} && binsof(rd_en_cp) intersect {0} && binsof(empty_cp) intersect {1};}

        wr_rd_overflow_cross : cross wr_en_cp , rd_en_cp , overflow_cp
                { ignore_bins write_read_01_with_overflow = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {1} && binsof(overflow_cp) intersect {1};
                  ignore_bins write_read_00_with_overflow = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {0} && binsof(overflow_cp) intersect {1};}

        wr_rd_underflow_cross : cross wr_en_cp , rd_en_cp , underflow_cp
                { ignore_bins write_read_10_with_underflow = binsof(wr_en_cp) intersect {1} && binsof(rd_en_cp) intersect {0} && binsof(underflow_cp) intersect {1};
                  ignore_bins write_read_00_with_underflow = binsof(wr_en_cp) intersect {0} && binsof(rd_en_cp) intersect {0} && binsof(underflow_cp) intersect {1};}

        wr_rd_almostfull_cross : cross wr_en_cp , rd_en_cp , almostfull_cp; 

        wr_rd_almostempty_cross : cross wr_en_cp , rd_en_cp , almostempty_cp;
endgroup

function new (string name = "FIFO_collector", uvm_component parent = null);
    super.new(name,parent);
    FIFO_cov_grp = new();
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
        cov_fifo.get(FIFO_seq_item);
        FIFO_cov_grp.sample();
    end
endtask

endclass