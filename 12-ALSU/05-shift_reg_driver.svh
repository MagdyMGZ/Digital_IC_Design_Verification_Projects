class shift_reg_driver extends uvm_driver #(shift_reg_seq_item);
    `uvm_component_utils(shift_reg_driver);
    
    virtual shift_reg_if shift_reg_vif;
    shift_reg_seq_item stim_seq_item;

    function new(string name="shift_reg_driver",uvm_component parent =null);
        super.new(name,parent);
    endfunction //new()

    task run_phase (uvm_phase phase);
    super.run_phase(phase);
        forever begin
            stim_seq_item = shift_reg_seq_item::type_id::create("stim_seq_item");
            seq_item_port.get_next_item(stim_seq_item);
            shift_reg_vif.direction = stim_seq_item.direction;
            shift_reg_vif.mode = stim_seq_item.mode;
            shift_reg_vif.serial_in = stim_seq_item.serial_in;
            shift_reg_vif.datain = stim_seq_item.datain;
            #2;
            seq_item_port.item_done();
           `uvm_info("run_phase",stim_seq_item.convert2string_stimulus(),UVM_HIGH);
        end
    endtask
endclass