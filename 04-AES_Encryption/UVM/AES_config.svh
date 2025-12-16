class AES_config extends uvm_object;

`uvm_object_utils(AES_config)

virtual AES_if AES_vif;
uvm_active_passive_enum sel_mode;

function new (string name = "AES_config");
    super.new(name);
endfunction

endclass