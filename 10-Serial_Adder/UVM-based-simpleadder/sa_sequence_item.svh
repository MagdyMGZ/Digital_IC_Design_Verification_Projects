class sa_sequence_item extends uvm_sequence_item;

`uvm_object_utils(sa_sequence_item)

rand bit [1:0] a;
rand bit [1:0] b;
     bit [2:0] out;

constraint a_c { a dist {0:/20, [1:3]:/80}; }

constraint b_c { b dist {0:/20, [1:3]:/80}; }

function new (string name = "sa_sequence_item");
    super.new(name);    
endfunction

function string convert2string ();
    return $sformatf ("%s a = %0d, b = %0d, out = %0d", super.convert2string(),a,b,out);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("%s a = %0d, b = %0d", super.convert2string(),a,b);
endfunction

endclass

class sa_sequence_item_change_constraints extends sa_sequence_item;

`uvm_object_utils(sa_sequence_item_change_constraints)

constraint a_c { a dist {0:/50, [1:3]:/50}; }

constraint b_c { b dist {0:/50, [1:3]:/50}; }

endclass