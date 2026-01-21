class ASYNCH_FIFO_config extends uvm_object;

`uvm_object_utils(ASYNCH_FIFO_config)

virtual ASYNCH_FIFO_if ASYNCH_FIFO_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "ASYNCH_FIFO_config");
    super.new(name);
endfunction

endclass