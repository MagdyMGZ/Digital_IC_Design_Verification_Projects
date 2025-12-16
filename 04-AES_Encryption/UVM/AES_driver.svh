class AES_driver extends uvm_driver #(AES_sequence_item);

`uvm_component_utils(AES_driver)

virtual AES_if AES_vif;
AES_sequence_item AES_seq_item;

function new (string name = "AES_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        AES_seq_item = AES_sequence_item::type_id::create("AES_seq_item");
        seq_item_port.get_next_item(AES_seq_item);
        AES_vif.in  = AES_seq_item.in;
        AES_vif.key = AES_seq_item.key;
        #5;
        seq_item_port.item_done();
        `uvm_info("run_phase",AES_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

endclass