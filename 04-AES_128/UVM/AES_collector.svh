class AES_collector extends uvm_subscriber #(AES_sequence_item);

`uvm_component_utils(AES_collector)

`uvm_analysis_imp_decl(_my_cov_collector)

uvm_analysis_imp_my_cov_collector #(AES_sequence_item, AES_collector) cov_export;

// AES_sequence_item AES_seq_item;

covergroup AES_cov_grp with function sample (AES_sequence_item AES_seq_item);
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
    // AES_seq_item = AES_sequence_item::type_id::create("AES_seq_item");
    cov_export = new("cov_export",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
endtask

function void write_my_cov_collector (AES_sequence_item AES_seq_item);
    // this.AES_seq_item = AES_seq_item;
    AES_cov_grp.sample(AES_seq_item);
endfunction

function void write (AES_sequence_item t);
    `uvm_info(get_type_name(),"Overriding the write function of the subscriber as it declared as a pure virtual function",UVM_DEBUG);
endfunction

endclass