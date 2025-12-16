class AES_collector extends uvm_component;

`uvm_component_utils(AES_collector)

uvm_analysis_port #(AES_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(AES_sequence_item) cov_fifo;

AES_sequence_item AES_seq_item;

covergroup AES_cov_grp;
      in_cp  : coverpoint AES_seq_item.in;
      key_cp : coverpoint AES_seq_item.key;
      out_cp : coverpoint AES_seq_item.out;
endgroup

function new (string name = "AES_collector", uvm_component parent = null);
    super.new(name,parent);
    AES_cov_grp = new();
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
        cov_fifo.get(AES_seq_item);
        AES_cov_grp.sample();
    end
endtask

endclass