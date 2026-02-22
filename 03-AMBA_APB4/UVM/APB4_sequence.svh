class APB4_sequence extends uvm_sequence #(APB4_sequence_item);

`uvm_object_utils(APB4_sequence)

APB4_sequence_item APB4_seq_item;

function new (string name = "APB4_sequence");
    super.new(name);    
endfunction

task body ();
    APB4_seq_item = APB4_sequence_item::type_id::create("APB4_seq_item");
    repeat (TESTS) begin
        start_item(APB4_seq_item);
        assert(APB4_seq_item.randomize());
        finish_item(APB4_seq_item);
    end
endtask

endclass
