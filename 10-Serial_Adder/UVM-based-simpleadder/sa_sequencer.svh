class sa_sequencer extends uvm_sequencer #(sa_sequence_item);

`uvm_component_utils(sa_sequencer)

function new (string name = "sa_sequencer", uvm_component parent = null);
    super.new(name,parent);
endfunction

endclass