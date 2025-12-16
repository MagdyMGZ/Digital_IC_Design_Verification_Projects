class AES_sequence extends uvm_sequence #(AES_sequence_item);

`uvm_object_utils(AES_sequence)

AES_sequence_item AES_seq_item;

function new (string name = "AES_sequence");
    super.new(name);    
endfunction

task body ();
    repeat(TESTS) begin
        AES_seq_item = AES_sequence_item::type_id::create("AES_seq_item");
        start_item(AES_seq_item);
        assert(AES_seq_item.randomize());
        finish_item(AES_seq_item);        
    end
endtask

endclass