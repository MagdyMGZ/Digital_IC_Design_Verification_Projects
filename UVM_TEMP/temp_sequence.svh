class temp_sequence extends uvm_sequence #(temp_sequence_item);

`uvm_object_utils(temp_sequence)

temp_sequence_item temp_seq_item;

function new (string name = "temp_sequence");
    super.new(name);    
endfunction

task body ();
    temp_seq_item = temp_sequence_item::type_id::create("temp_seq_item");
    repeat (TESTS) begin
        start_item(temp_seq_item);
        assert(temp_seq_item.randomize());
        finish_item(temp_seq_item);
    end
endtask

endclass
