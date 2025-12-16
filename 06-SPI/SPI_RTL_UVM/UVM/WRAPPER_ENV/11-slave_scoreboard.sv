package slave_scoreboard_pkg;
import slave_seq_item_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"
class slave_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(slave_scoreboard);
    uvm_analysis_export #(slave_seq_item) sb_export;
    uvm_tlm_analysis_fifo #(slave_seq_item) sb_fifo;
    slave_seq_item seq_item_sb;
    
    int error_count;
    int correct_count;
    
    function new(string name = "slave_scoreboard", uvm_component parent = null);
        super.new(name,parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        sb_export = new("sb_export",this);
        sb_fifo = new("sb_fifo",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        sb_export.connect(sb_fifo.analysis_export);
    endfunction

    task run_phase (uvm_phase phase);
        super.run_phase(phase);
            forever begin
                sb_fifo.get(seq_item_sb);
                if ((seq_item_sb.rx_data !== seq_item_sb.rx_data_gm) || (seq_item_sb.rx_valid !== seq_item_sb.rx_valid_gm) || (seq_item_sb.MISO !== seq_item_sb.MISO_gm)) begin
                    `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s while the refecrence rx_data: %0d, rx_valid: %0b, MISO: %0b",
                        seq_item_sb.convert2string(),seq_item_sb.rx_data_gm,seq_item_sb.rx_valid_gm,seq_item_sb.MISO_gm));
                    error_count++;
                end
                else begin
                    `uvm_info("run_phase",$sformatf("correct slave_out : %s",seq_item_sb.convert2string()),UVM_HIGH);     
                     correct_count++; 
                end
            end
    endtask

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("report_phase",$sformatf("Slave: Total successful counts : %0d",correct_count),UVM_MEDIUM);     
        `uvm_info("report_phase",$sformatf("Slave: Total failed counts : %0d",error_count),UVM_MEDIUM);     
    endfunction
endclass
endpackage

