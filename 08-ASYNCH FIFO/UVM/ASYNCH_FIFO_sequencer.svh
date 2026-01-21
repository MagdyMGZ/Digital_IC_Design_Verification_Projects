class ASYNCH_FIFO_sequencer extends uvm_sequencer #(ASYNCH_FIFO_sequence_item);

`uvm_component_utils(ASYNCH_FIFO_sequencer)

function new (string name = "ASYNCH_FIFO_sequencer", uvm_component parent = null);
    super.new(name,parent);
endfunction

endclass