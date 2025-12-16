class FIFO_sequence_item extends uvm_sequence_item;

`uvm_object_utils(FIFO_sequence_item)

// Inputs Declaration
rand logic [FIFO_WIDTH-1:0] data_in;
rand logic wr_en, rd_en, rst_n;

// Outputs Declaration
logic [FIFO_WIDTH-1:0] data_out;
logic full, almostfull, empty, almostempty, overflow, underflow, wr_ack;

// Constraint Blocks
constraint rst_n_c {rst_n dist { 0 :/ 2 , 1 :/ 98 };}

constraint wr_en_c {wr_en dist { 1 :/ 70 , 0 :/ 30 };}

constraint rd_en_c {rd_en dist { 1 :/ 30 , 0 :/ 70 };}

// Additional constraint block for write operation only
constraint write_only { rst_n == 1;  wr_en == 1;  rd_en == 0; } 

// Additional constraint block for read operation only
constraint read_only { rst_n == 1;  wr_en == 0;  rd_en == 1; } 

function new (string name = "FIFO_sequence_item");
    super.new(name);    
endfunction

function string convert2string ();
    return $sformatf ("%s data_in = %0d, wr_en = %0d, rd_en = %0d, rst_n = %0d, data_out = %0d, full = %0d, almostfull = %0d, empty = %0d, almostempty = %0d, overflow = %0d, underflow = %0d, wr_ack = %0d", super.convert2string(),data_in,wr_en,rd_en,rst_n,data_out,full,almostfull,empty,almostempty,overflow,underflow,wr_ack);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("%s data_in = %0d, wr_en = %0d, rd_en = %0d, rst_n = %0d", super.convert2string(),data_in,wr_en,rd_en,rst_n);
endfunction

endclass
