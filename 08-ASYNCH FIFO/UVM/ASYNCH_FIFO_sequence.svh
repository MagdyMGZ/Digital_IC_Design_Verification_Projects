class ASYNCH_FIFO_reset_sequence extends uvm_sequence #(ASYNCH_FIFO_sequence_item);

`uvm_object_utils(ASYNCH_FIFO_reset_sequence)

ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;

function new (string name = "ASYNCH_FIFO_reset_sequence");
    super.new(name);    
endfunction

task body ();
    ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");
    start_item(ASYNCH_FIFO_seq_item);
    ASYNCH_FIFO_seq_item.i_rst_n = 0;
    ASYNCH_FIFO_seq_item.i_wen   = 0;
    ASYNCH_FIFO_seq_item.i_ren   = 0;
    ASYNCH_FIFO_seq_item.i_wdata = 0;
    finish_item(ASYNCH_FIFO_seq_item);
endtask

endclass

class ASYNCH_FIFO_main_sequence extends uvm_sequence #(ASYNCH_FIFO_sequence_item);

`uvm_object_utils(ASYNCH_FIFO_main_sequence)

ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;

function new (string name = "ASYNCH_FIFO_main_sequence");
    super.new(name);    
endfunction

task body ();
    // Write Sequence
    ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");
    repeat(TESTS/2) begin
        ASYNCH_FIFO_seq_item.constraint_mode(0);
        ASYNCH_FIFO_seq_item.write_only.constraint_mode(1);
        start_item(ASYNCH_FIFO_seq_item);
        assert(ASYNCH_FIFO_seq_item.randomize());
        finish_item(ASYNCH_FIFO_seq_item);        
    end

    // Read Sequence
    ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");
    repeat(TESTS/4) begin
        ASYNCH_FIFO_seq_item.constraint_mode(0);
        ASYNCH_FIFO_seq_item.read_only.constraint_mode(1);
        ASYNCH_FIFO_seq_item.i_wdata.rand_mode(0);   // we disable the randomization for the data_in as in the read mode we don't need it
        start_item(ASYNCH_FIFO_seq_item);
        assert(ASYNCH_FIFO_seq_item.randomize());
        finish_item(ASYNCH_FIFO_seq_item);      
    end

    // Read & Write Sequence
    ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");
    repeat(TESTS/4) begin
        ASYNCH_FIFO_seq_item.constraint_mode(1);
        ASYNCH_FIFO_seq_item.read_only.constraint_mode(0);
        ASYNCH_FIFO_seq_item.write_only.constraint_mode(0);
        ASYNCH_FIFO_seq_item.i_wdata.rand_mode(1);
        start_item(ASYNCH_FIFO_seq_item);
        assert(ASYNCH_FIFO_seq_item.randomize());
        finish_item(ASYNCH_FIFO_seq_item);
    end
endtask

endclass