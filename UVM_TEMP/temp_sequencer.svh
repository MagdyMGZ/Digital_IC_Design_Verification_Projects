class temp_sequencer extends uvm_sequencer #(temp_sequence_item);

`uvm_component_utils(temp_sequencer)

function new (string name = "temp_sequencer", uvm_component parent = null);
    super.new(name,parent);
endfunction

endclass