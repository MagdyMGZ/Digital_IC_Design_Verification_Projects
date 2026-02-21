class sa_sequence extends uvm_sequence #(sa_sequence_item);

`uvm_object_utils(sa_sequence)

sa_sequence_item sa_seq_item;

function new (string name = "sa_sequence");
    super.new(name);    
endfunction

task body ();
    repeat(TESTS) begin
        sa_seq_item = sa_sequence_item::type_id::create("sa_seq_item");
        start_item(sa_seq_item);
        assert(sa_seq_item.randomize());
        finish_item(sa_seq_item);        
    end
endtask

endclass