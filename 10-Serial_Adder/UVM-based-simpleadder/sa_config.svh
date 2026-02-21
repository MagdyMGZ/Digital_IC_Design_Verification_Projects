class sa_config extends uvm_object;

`uvm_object_utils(sa_config)

virtual sa_if sa_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "sa_config");
    super.new(name);
endfunction

endclass