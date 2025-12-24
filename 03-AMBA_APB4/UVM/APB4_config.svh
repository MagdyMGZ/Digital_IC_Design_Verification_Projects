class APB4_config extends uvm_object;

`uvm_object_utils(APB4_config)

virtual APB4_BFM_if APB4_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "APB4_config");
    super.new(name);
endfunction

endclass