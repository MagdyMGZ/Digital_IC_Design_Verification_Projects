class APB4_driver extends uvm_driver #(APB4_sequence_item);

`uvm_component_utils(APB4_driver)

virtual APB4_BFM_if APB4_vif;
APB4_sequence_item APB4_seq_item;

function new (string name = "APB4_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    
    `uvm_info(get_type_name(),"Reset Asserted",UVM_LOW)
    APB4_vif.reset();
    `uvm_info(get_type_name(),"Reset Deasserted",UVM_LOW)

    forever begin
        APB4_seq_item = APB4_sequence_item::type_id::create("APB4_seq_item");
        seq_item_port.get_next_item(APB4_seq_item);
        drive(APB4_seq_item);
        seq_item_port.item_done();
        `uvm_info("run_phase",APB4_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

virtual task drive (APB4_sequence_item APB4_seq_item);
    if (APB4_seq_item.kind == write)
        APB4_vif.write(APB4_seq_item.PRESETn, APB4_seq_item.TRANSFER, APB4_seq_item.ADDR, APB4_seq_item.WDATA, APB4_seq_item.STRB);
    else if (APB4_seq_item.kind == read)
        APB4_vif.read(APB4_seq_item.PRESETn, APB4_seq_item.TRANSFER, APB4_seq_item.ADDR, APB4_seq_item.STRB);
endtask

endclass