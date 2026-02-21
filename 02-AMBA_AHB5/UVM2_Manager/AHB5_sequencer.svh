class AHB5_sequencer extends uvm_sequencer #(AHB5_sequence_item);

`uvm_component_utils(AHB5_sequencer)

function new (string name = "AHB5_sequencer", uvm_component parent = null);
    super.new(name,parent);
endfunction

endclass