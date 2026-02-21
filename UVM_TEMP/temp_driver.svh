class temp_driver extends uvm_driver #(temp_sequence_item);

`uvm_component_utils(temp_driver)

virtual temp_if temp_vif;
temp_sequence_item temp_seq_item;

function new (string name = "temp_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        temp_seq_item = temp_sequence_item::type_id::create("temp_seq_item");
        seq_item_port.get_next_item(temp_seq_item);
        
        // Blocking Event
        
        seq_item_port.item_done();
        `uvm_info("run_phase",temp_seq_item.convert2string_stimulus(),UVM_HIGH)
    end
endtask

endclass