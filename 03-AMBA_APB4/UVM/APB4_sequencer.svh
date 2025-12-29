class APB4_sequencer extends uvm_sequencer #(APB4_sequence_item);

`uvm_component_utils(APB4_sequencer)

function new (string name = "APB4_sequencer", uvm_component parent = null);
    super.new(name,parent);
endfunction

endclass