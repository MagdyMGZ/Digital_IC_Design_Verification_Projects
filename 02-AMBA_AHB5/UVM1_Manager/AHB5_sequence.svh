class AHB5_sequence extends uvm_sequence #(AHB5_sequence_item);

`uvm_object_utils(AHB5_sequence)

AHB5_sequence_item AHB5_seq_item;

function new (string name = "AHB5_sequence");
    super.new(name);    
endfunction

task body ();
    AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
    repeat (TESTS) begin
        start_item(AHB5_seq_item);
        assert(AHB5_seq_item.randomize());
        finish_item(AHB5_seq_item);
    end
endtask

endclass
