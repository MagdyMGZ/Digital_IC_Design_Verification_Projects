class AES_sequence_item extends uvm_sequence_item;

`uvm_object_utils(AES_sequence_item)

rand logic [N-1:0] in;
rand logic [N-1:0] key;
     logic [N-1:0] out;

function new (string name = "AES_sequence_item");
    super.new(name);    
endfunction

function string convert2string ();
    return $sformatf ("%s in = %0h, key = %0h, out = %0h", 
        super.convert2string(), in, key, out);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("in = %0h, key = %0h", in, key);
endfunction

endclass
