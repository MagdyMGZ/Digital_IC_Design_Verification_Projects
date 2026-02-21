class AHB5_reactive_sequence extends uvm_sequence #(AHB5_sequence_item);

`uvm_object_utils(AHB5_reactive_sequence)

AHB5_sequence_item AHB5_seq_item;

function new (string name = "AHB5_reactive_sequence");
    super.new(name);    
endfunction

task body ();
    AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
    start_item(AHB5_seq_item);
    assert(AHB5_seq_item.randomize());
    finish_item(AHB5_seq_item);
    repeat (TESTS) begin
        get_response(AHB5_seq_item); 
        if (AHB5_seq_item.trans_done) begin
            start_item(AHB5_seq_item);
            assert(AHB5_seq_item.randomize());
            finish_item(AHB5_seq_item);
        end
    end
endtask

endclass