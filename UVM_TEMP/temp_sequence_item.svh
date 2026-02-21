class temp_sequence_item extends uvm_sequence_item;

`uvm_object_utils(temp_sequence_item)

// Signals Declaration
logic Signals;

function new (string name = "temp_sequence_item");
    super.new(name);
endfunction

function string convert2string ();
    return $sformatf ("%s Signals = %0d", super.convert2string(), Signals);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("Signals = %0d", Signals);
endfunction

endclass
