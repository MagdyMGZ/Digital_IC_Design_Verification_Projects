package ram_coverage_pkg;
    import ram_seq_item_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    class ram_coverage extends uvm_component;
        `uvm_component_utils(ram_coverage)
        uvm_analysis_port #(ram_seq_item) cov_export;
        uvm_tlm_analysis_fifo #(ram_seq_item) cov_fifo;
        ram_seq_item seq_item_cov;

        covergroup cvr_grp;
            // 1- Write Coverpoint to check transaction ordering for din[9:8]: 
            // • Check din[9:8] takes 4 possible values
            // • Check write data after write address
            // • Check read data after read address
            // • Check write address => write data => read address => read data
            ram_order_cp : coverpoint seq_item_cov.din[9:8] {
                bins write_add        = {2'b00};
                bins write_data       = {2'b01};
                bins read_add         = {2'b10};
                bins read_data        = {2'b11};
                bins write_only_trans = (2'b00 => 2'b01);
                bins read_only_trans  = (2'b10 => 2'b11);
            }
            rstn_cp : coverpoint seq_item_cov.rst_n;
            rx_valid_cp : coverpoint seq_item_cov.rx_valid;
            tx_valid_cp : coverpoint seq_item_cov.tx_valid;
            
            // 2- Cross coverage:
            // • Between all bins of din[9:8] and rx_valid signal when it is high
            rx_valid_cross_ram_order : cross ram_order_cp, rx_valid_cp {
                ignore_bins ign_bin_1 = binsof(rx_valid_cp) intersect {0};
                ignore_bins ign_bin_2 = binsof(ram_order_cp.write_only_trans);
                ignore_bins ign_bin_3 = binsof(ram_order_cp.read_only_trans);
            }
            
            // • Between din[9:8] when it equals read data and tx_valid when it is high
            tx_valid_cross_ram_order : cross ram_order_cp, tx_valid_cp {
                bins read_data = binsof(ram_order_cp.read_data) && binsof(tx_valid_cp) intersect {1};
                option.cross_auto_bin_max = 0;
            }
        endgroup 

        function new (string name = "ram_coverage", uvm_component parent = null);
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

