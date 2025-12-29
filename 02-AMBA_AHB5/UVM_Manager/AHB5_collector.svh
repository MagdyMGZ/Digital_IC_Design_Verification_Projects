class AHB5_collector extends uvm_component;

`uvm_component_utils(AHB5_collector)

uvm_analysis_port #(AHB5_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(AHB5_sequence_item) cov_fifo;

AHB5_sequence_item AHB5_seq_item;

covergroup AHB5_cov_grp;
    hresetn_cp : coverpoint AHB5_seq_item.HRESETn { 
        bins presetn0 = {0};
        bins presetn1 = {1};
    }
    slv_hsel_cp : coverpoint AHB5_seq_item.HSEL1 {
        bins slv_closed = {0};
        bins slv_opened = {1};
    }
    slv_hready_cp : coverpoint AHB5_seq_item.HREADY {
        bins slv_ready0 = {0};
        bins slv_ready1 = {1};
    }
    haddr_cp : coverpoint AHB5_seq_item.HADDR {
        bins memory_slv_addr[] = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60};
    }
    hburst_cp : coverpoint AHB5_seq_item.HBURST {
        bins hburst_values[] = {SINGLE, INCR, WRAP4, INCR4, WRAP8, INCR8, WRAP16, INCR16};
    }
    hsize_cp : coverpoint AHB5_seq_item.HSIZE {
        bins hsize_values[] = {BYTE, HALFWORD, WORD};
    }
    htrans_cp : coverpoint AHB5_seq_item.HTRANS {
        bins htrans_values[] = {IDLE, BUSY, NONSEQ, SEQ};
    }
    hwdata_cp : coverpoint AHB5_seq_item.HWDATA {
        bins zero = {32'b0};
        bins max = {32'hFFFFFFFF};
        bins typical = {[32'h1:32'hFFFFFFFE]};
    }
    hstrb_cp : coverpoint AHB5_seq_item.HWSTRB {
        bins one_hot_strb[] = {4'b1000, 4'b0100, 4'b0010, 4'b0001};
        bins strb0 = {0};
        bins strb1 = {4'b1111};
    }
    hwrite_cp : coverpoint AHB5_seq_item.HWRITE {
        bins hread = {READ};
        bins hwrite = {WRITE};
    }
    hreadyout_cp : coverpoint AHB5_seq_item.HREADYOUT {
        bins hreadyout0 = {0};
        bins hreadyout1 = {1};
    }
    hresp_cp : coverpoint AHB5_seq_item.HRESP {
        bins okay = {0};
        illegal_bins error = {1};
    }
endgroup

function new (string name = "AHB5_collector", uvm_component parent = null);
    super.new(name,parent);
    AHB5_cov_grp = new();
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
        cov_fifo.get(AHB5_seq_item);
        AHB5_cov_grp.sample();
    end
endtask

function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("Functional Coverage = %0.0f", AHB5_cov_grp.get_coverage()), UVM_MEDIUM)
endfunction

endclass