class ALSU_config_obj extends uvm_object;

`uvm_object_utils(ALSU_config_obj);

virtual ALSU_if alsu_vif;
uvm_active_passive_enum sel_mod;

function new (string name="ALSU_config_obj");
    super.new(name);
endfunction //new()

endclass