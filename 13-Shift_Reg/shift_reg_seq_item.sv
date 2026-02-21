package shift_reg_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class shift_reg_seq_item extends uvm_sequence_item;
    `uvm_object_utils(shift_reg_seq_item);

    rand bit serial_in;
    rand bit direction;
    rand bit mode;
    rand bit [5:0]datain;
    rand bit reset;
    bit [5:0] dataout;

    function new(string name = "shift_reg_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s diretion=%0b,mode=%0b,serial_in=%0b,datain=%0d,dataout=%0d",
            super.convert2string(),direction,mode,serial_in,datain,dataout);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("%s diretion=%0b,mode=%0b,serial_in=%0b,datain=%0d",
            super.convert2string(),direction,mode,serial_in,datain);
    endfunction

    constraint rst_con {
        reset dist {1 :/ 2, 0 :/ 98};
    }
endclass

class shift_reg_seq_item_disable_rst extends shift_reg_seq_item;
    `uvm_object_utils(shift_reg_seq_item_disable_rst);
    function new(string name = "shift_reg_seq_item");
        super.new(name);
    endfunction

    constraint rst_c {
        reset == 0;
    }
endclass
endpackage

