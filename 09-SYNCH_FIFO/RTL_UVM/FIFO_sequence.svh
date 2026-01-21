class FIFO_reset_sequence extends uvm_sequence #(FIFO_sequence_item);

`uvm_object_utils(FIFO_reset_sequence)

FIFO_sequence_item FIFO_seq_item;

function new (string name = "FIFO_reset_sequence");
    super.new(name);    
endfunction

task body ();
    FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
    start_item(FIFO_seq_item);
    FIFO_seq_item.rst_n   = 0;
    FIFO_seq_item.wr_en   = 0;
    FIFO_seq_item.rd_en   = 0;
    FIFO_seq_item.data_in = 0;
    finish_item(FIFO_seq_item);
endtask

endclass

class FIFO_main_sequence extends uvm_sequence #(FIFO_sequence_item);

`uvm_object_utils(FIFO_main_sequence)

FIFO_sequence_item FIFO_seq_item;

function new (string name = "FIFO_main_sequence");
    super.new(name);    
endfunction

task body ();
    // Write Sequence
    repeat(TESTS/2) begin
        FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
        start_item(FIFO_seq_item);
        FIFO_seq_item.constraint_mode(0);
        FIFO_seq_item.write_only.constraint_mode(1);
        assert(FIFO_seq_item.randomize());
        finish_item(FIFO_seq_item);        
    end

    // Read Sequence
    repeat(TESTS/4) begin
        FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
        start_item(FIFO_seq_item);
        FIFO_seq_item.constraint_mode(0);
        FIFO_seq_item.read_only.constraint_mode(1);
        FIFO_seq_item.data_in.rand_mode(0);   // we disable the randomization for the data_in as in the read mode we don't need it
        assert(FIFO_seq_item.randomize());
        finish_item(FIFO_seq_item);      
    end

    // Read & Write Sequence
    repeat(TESTS/4) begin
        FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
        start_item(FIFO_seq_item);
        FIFO_seq_item.constraint_mode(1);
        FIFO_seq_item.read_only.constraint_mode(0);
        FIFO_seq_item.write_only.constraint_mode(0);
        FIFO_seq_item.data_in.rand_mode(1); 
        assert(FIFO_seq_item.randomize());
        finish_item(FIFO_seq_item);      
    end
endtask

endclass