class AHB5_driver extends uvm_driver #(AHB5_sequence_item);

`uvm_component_utils(AHB5_driver)

virtual AHB5_BFM_if AHB5_vif;
AHB5_sequence_item AHB5_seq_item;

function new (string name = "AHB5_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    
    `uvm_info(get_type_name(),"Reset Asserted",UVM_LOW)
    AHB5_vif.reset();
    `uvm_info(get_type_name(),"Reset Deasserted",UVM_LOW)

    forever begin
        AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
        seq_item_port.get_next_item(AHB5_seq_item);
        drive(AHB5_seq_item);
        seq_item_port.item_done();
        `uvm_info("run_phase",AHB5_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

virtual task drive (AHB5_sequence_item AHB5_seq_item);
    if (AHB5_seq_item.HWRITE == WRITE)
        AHB5_vif.write(AHB5_seq_item.HRESETn, AHB5_seq_item.HSEL1, AHB5_seq_item.HREADY, AHB5_seq_item.HADDR, AHB5_seq_item.HBURST, AHB5_seq_item.HSIZE, AHB5_seq_item.HTRANS, AHB5_seq_item.HWDATA, AHB5_seq_item.HWSTRB);
    else if (AHB5_seq_item.HWRITE == READ)
        AHB5_vif.read(AHB5_seq_item.HRESETn, AHB5_seq_item.HSEL1, AHB5_seq_item.HREADY, AHB5_seq_item.HADDR, AHB5_seq_item.HBURST, AHB5_seq_item.HSIZE, AHB5_seq_item.HTRANS, AHB5_seq_item.HWSTRB);
endtask

endclass