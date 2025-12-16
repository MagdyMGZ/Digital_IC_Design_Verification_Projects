package wrapper_coverage_pkg;
    import wrapper_seq_item_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    class wrapper_coverage extends uvm_component;
        `uvm_component_utils(wrapper_coverage)
        uvm_analysis_port #(wrapper_seq_item) cov_export;
        uvm_tlm_analysis_fifo #(wrapper_seq_item) cov_fifo;
        wrapper_seq_item seq_item_cov;

        covergroup cvr_grp;
            rstn_cp : coverpoint seq_item_cov.rst_n;
            SS_n_cp : coverpoint seq_item_cov.SS_n {
                bins ss_n_trans = (1=>0[*13]=>1);
                bins ss_n_trans_read_data = (1=>0[*23]=>1);
                bins ss_n_start_trans = (1=>0);
                bins ss_n_end_trans = (0=>1);
            }
            MOSI_cp: coverpoint seq_item_cov.MOSI {
                bins wr_addr_trans = (0=>0=>0);
                bins wr_data_trans = (0=>0=>1);
                bins rd_addr_trans = (1=>1=>0);
                bins rd_data_trans = (1=>1=>1);
            }
            MISO_cp: coverpoint seq_item_cov.MISO;
            ss_n_op_cross: cross SS_n_cp, MOSI_cp {
                ignore_bins bin_1 = binsof(SS_n_cp.ss_n_trans);
                ignore_bins bin_2 = binsof(SS_n_cp.ss_n_trans_read_data);
                ignore_bins bin_3 = binsof(SS_n_cp.ss_n_end_trans);
            }
        endgroup 

        function new (string name = "wrapper_coverage", uvm_component parent = null);
            super.new(name,parent);
            cvr_grp = new();            
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
                cov_fifo.get(seq_item_cov);
                cvr_grp.sample();
            end
        endtask
    endclass
endpackage

