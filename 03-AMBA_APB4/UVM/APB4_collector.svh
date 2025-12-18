class APB4_collector extends uvm_component;

`uvm_component_utils(APB4_collector)

uvm_analysis_port #(APB4_sequence_item) cov_export;
uvm_tlm_analysis_fifo #(APB4_sequence_item) cov_fifo;

APB4_sequence_item APB4_seq_item;

covergroup APB4_cov_grp;
    type_cp : coverpoint APB4_seq_item.kind {
        bins read = {0};
        bins write = {1};
    }
    slave_cp : coverpoint APB4_seq_item.slave {
        bins regfile_slv0 = {0};
        bins memory_slv1 = {1};
    }
    presetn_cp : coverpoint APB4_seq_item.PRESETn { 
        bins presetn0 = {0};
        bins presetn1 = {1};
    }
    transfer_cp : coverpoint APB4_seq_item.TRANSFER {
        bins no_transfer = {0};
        bins transfer_done = {1};
    }
    write_cp : coverpoint APB4_seq_item.WRITE {
        bins pread = {0};
        bins pwrite = {1};
    }
    strb_cp : coverpoint APB4_seq_item.STRB {
        bins one_hot_strb[] = {4'b1000, 4'b0100, 4'b0010, 4'b0001};
        bins strb0 = {0};
        bins strb1 = {4'b1111};
    }
    addr_slv0_cp : coverpoint APB4_seq_item.ADDR iff (!APB4_seq_item.kind) {
        bins regfile_slv0_addr[] = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60};
    }
    addr_slv1_cp : coverpoint APB4_seq_item.ADDR[ADDR_WIDTH-1] iff (APB4_seq_item.kind) {
        bins memory_slv1_addr = {1'b1};
    }
    wdata_cp : coverpoint APB4_seq_item.WDATA {
        bins zero = {32'b0};
        bins max = {32'hFFFFFFFF};
        bins typical = {[32'h1:32'hFFFFFFFE]};
    }
    regfile_slv0_addr : cross slave_cp, addr_slv0_cp {
        option.cross_auto_bin_max = 0;
        bins regfile_addr = binsof(slave_cp.regfile_slv0) && binsof(addr_slv0_cp.regfile_slv0_addr);
    }
    memory_slv1_addr : cross slave_cp, addr_slv1_cp {
        option.cross_auto_bin_max = 0;
        bins memory_addr = binsof(slave_cp.memory_slv1) && binsof(addr_slv1_cp.memory_slv1_addr);
    }
endgroup

function new (string name = "APB4_collector", uvm_component parent = null);
    super.new(name,parent);
    APB4_cov_grp = new();
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
        cov_fifo.get(APB4_seq_item);
        APB4_cov_grp.sample();
    end
endtask

endclass