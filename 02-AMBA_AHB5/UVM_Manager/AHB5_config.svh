class AHB5_config extends uvm_object;

`uvm_object_utils(AHB5_config)

virtual AHB5_BFM_if AHB5_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "AHB5_config");
    super.new(name);
endfunction

endclass