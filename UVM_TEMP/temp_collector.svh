class temp_collector extends uvm_component;

`uvm_component_utils(temp_collector)

uvm_analysis_port #(temp_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(temp_sequence_item) cov_fifo;

temp_sequence_item temp_seq_item;

covergroup temp_cov_grp;

endgroup

function new (string name = "temp_collector", uvm_component parent = null);
    super.new(name,parent);
    temp_cov_grp = new();
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
        cov_fifo.get(temp_seq_item);
        temp_cov_grp.sample();
    end
endtask

function void report_phase (uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("report_phase", $sformatf("Functional Coverage = %0.0f", temp_cov_grp.get_coverage()), UVM_MEDIUM)
endfunction

endclass