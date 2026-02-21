class AES_sequence_item extends uvm_sequence_item;

rand logic [N-1:0] in;
rand logic [N-1:0] key;
     logic [N-1:0] out;

`uvm_object_utils_begin(AES_sequence_item)
  `uvm_field_int(in , UVM_HEX)
  `uvm_field_int(key, UVM_ALL_ON)
  `uvm_field_int(out, UVM_DEFAULT)
`uvm_object_utils_end

function new (string name = "AES_sequence_item");
    super.new(name);    
endfunction

function void do_print(uvm_printer printer);
    `uvm_info(get_type_name(),"My do print", UVM_HIGH)
endfunction

function void do_copy(uvm_object rhs);
    `uvm_info(get_type_name(),"My do copy", UVM_HIGH)
endfunction

function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    `uvm_info(get_type_name(),"My do compare", UVM_HIGH)
    return super.do_compare(rhs,comparer);
endfunction

function void do_record(uvm_recorder recorder);
    `uvm_info(get_type_name(),"My do record", UVM_HIGH)
endfunction

function string convert2string ();
    return $sformatf ("%s in = %0h, key = %0h, out = %0h", 
        super.convert2string(), in, key, out);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("in = %0h, key = %0h", in, key);
endfunction

endclass

class AES_sequence_item_without_field_macros extends uvm_sequence_item;

`uvm_object_utils(AES_sequence_item_without_field_macros)

rand logic [N-1:0] in;
rand logic [N-1:0] key;
     logic [N-1:0] out;

function new (string name = "AES_sequence_item_without_field_macros");
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