class temp_config extends uvm_object;

`uvm_object_utils(temp_config)

virtual temp_if temp_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "temp_config");
    super.new(name);
endfunction

endclass