class ASYNCH_FIFO_sequence_item extends uvm_sequence_item;

`uvm_object_utils(ASYNCH_FIFO_sequence_item)

    // Signals Declaration
rand    logic                  i_rst_n;
rand    logic                  i_wen;
rand    logic [FIFO_WIDTH-1:0] i_wdata;
rand    logic                  i_ren;
        logic                  o_full;
        logic                  o_empty;
        logic [FIFO_WIDTH-1:0] o_rdata;

        logic                  o_full_gold;
        logic                  o_empty_gold;
        logic [FIFO_WIDTH-1:0] o_rdata_gold;

// Constraint Blocks
constraint rst_n_c {i_rst_n dist { 0 :/ 2 , 1 :/ 98 };}

constraint wr_en_c {i_wen dist { 1 :/ 70 , 0 :/ 30 };}

constraint rd_en_c {i_ren dist { 1 :/ 30 , 0 :/ 70 };}

// Additional constraint block for write operation only
constraint write_only { i_rst_n == 1; i_wen == 1; i_ren == 0; } 

// Additional constraint block for read operation only
constraint read_only { i_rst_n == 1; i_wen == 0; i_ren == 1; } 

function new (string name = "ASYNCH_FIFO_sequence_item");
    super.new(name);    
endfunction

function string convert2string ();
    return $sformatf ("%s i_wdata = %0d, i_wen = %0d, i_ren = %0d, i_rst_n = %0d, o_rdata = %0d, o_full = %0d, o_empty = %0d", super.convert2string(),i_wdata,i_wen,i_ren,i_rst_n,o_rdata,o_full,o_empty);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("i_wdata = %0d, i_wen = %0d, i_ren = %0d, i_rst_n = %0d",i_wdata,i_wen,i_ren,i_rst_n);
endfunction

endclass
