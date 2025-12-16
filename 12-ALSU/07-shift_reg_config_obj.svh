class shift_reg_config_obj extends uvm_object;

`uvm_object_utils(shift_reg_config_obj);

virtual shift_reg_if shift_reg_vif;
uvm_active_passive_enum sel_mod;

function new (string name = "shift_reg_config_obj");
    super.new(name);
endfunction //new()

endclass