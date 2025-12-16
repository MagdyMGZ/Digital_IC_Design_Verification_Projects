class shift_reg_main_sequence extends uvm_sequence #(shift_reg_seq_item);
   `uvm_object_utils(shift_reg_main_sequence);

   shift_reg_seq_item seq_item;
      function new(string name="shift_reg_main_sequence");
         super.new(name);
      endfunction 

      task body;
         seq_item = shift_reg_seq_item::type_id::create("seq_item");
         repeat(1000) begin
            start_item(seq_item);
            assert (seq_item.randomize());
            finish_item(seq_item);    
         end
      endtask      
endclass