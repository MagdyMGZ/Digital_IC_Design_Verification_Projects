class sa_collector extends uvm_component;

`uvm_component_utils(sa_collector)

uvm_analysis_port #(sa_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(sa_sequence_item) cov_fifo;

sa_sequence_item sa_seq_item;

covergroup sa_cov_grp;
    a_cp: coverpoint sa_seq_item.a {bins a_0 = {0};
                              bins a_1 = {1};
                              bins a_2 = {2};
                              bins a_3 = {3};
                              bins a_trans[] = (0=>1),(1=>2),(2=>3);}

    b_cp: coverpoint sa_seq_item.b {bins b_0 = {0};
                              bins b_1 = {1};
                              bins b_2 = {2};
                              bins b_3 = {3};
                              bins b_trans[] = (0=>1),(1=>2),(2=>3);}

    out_cp: coverpoint sa_seq_item.out {ignore_bins max_out = {7};}
    axb: cross sa_seq_item.a, sa_seq_item.b;
endgroup

function new (string name = "sa_collector", uvm_component parent = null);
    super.new(name,parent);
    sa_cov_grp = new();
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
        cov_fifo.get(sa_seq_item);
        sa_cov_grp.sample();
    end
endtask

endclass