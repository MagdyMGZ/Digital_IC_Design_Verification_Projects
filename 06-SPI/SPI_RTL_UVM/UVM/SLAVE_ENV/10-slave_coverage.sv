package slave_coverage_pkg;
    import slave_seq_item_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    class slave_coverage extends uvm_component;
        `uvm_component_utils(slave_coverage)
        uvm_analysis_port #(slave_seq_item) cov_export;
        uvm_tlm_analysis_fifo #(slave_seq_item) cov_fifo;
        slave_seq_item seq_item_cov;

        covergroup cvr_grp;

            // 1- Add coverpoints on rx_data[9:8] to take all possible values and all possible transitions
            rx_data_cp : coverpoint seq_item_cov.rx_data[9:8]{
                bins wr_addr = {2'b00};
                bins wr_data = {2'b01};
                bins rd_addr = {2'b10};
                bins rd_data = {2'b11};
                bins write_trans = (2'b00 => 2'b01);
                bins read_trans  = (2'b10 => 2'b11);
            }
            // 2- Add coverpoints on SS_n to capture:
            // A. Check full transaction duration: 1 → 0 [*13] → 1 for normal operations.
            // B. Check extended transaction: 1 → 0 [*23] → 1 for READ_DATA
            SS_n_cp : coverpoint seq_item_cov.SS_n {
                bins ss_n_trans = (1=>0[*13]=>1);
                bins ss_n_trans_read_data = (1=>0[*23]=>1);
                bins ss_n_start_trans = (1=>0);
                bins ss_n_end_trans = (0=>1);
            }
            // 3- Add coverpoints on MOSI to validate correct transitions: 
            // A. 000 (Write Address) 
            // B. 001 (Write Data) 
            // C. 110 (Read Address) 
            // D. 111 (Read Data)
            MOSI_cp: coverpoint seq_item_cov.MOSI {
                bins wr_addr_trans = (0=>0=>0);
                bins wr_data_trans = (0=>0=>1);
                bins rd_addr_trans = (1=>1=>0);
                bins rd_data_trans = (1=>1=>1);
            }
            // 4- Cross coverage between SS_n and MOSI bins (Exclude irrelevant bins to focus on legal operation scenarios)
            MISO_cp: coverpoint seq_item_cov.MISO;
            ss_n_op_cross: cross SS_n_cp, MOSI_cp {
                ignore_bins bin_1 = binsof(SS_n_cp.ss_n_trans);
                ignore_bins bin_2 = binsof(SS_n_cp.ss_n_trans_read_data);
                ignore_bins bin_3 = binsof(SS_n_cp.ss_n_end_trans);
            }
            rstn_cp : coverpoint seq_item_cov.rst_n;
            rx_valid_cp : coverpoint seq_item_cov.rx_valid;
            tx_valid_cp : coverpoint seq_item_cov.tx_valid;
        endgroup 

        function new (string name = "slave_coverage", uvm_component parent = null);
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

