class AES_config extends uvm_object;

virtual AES_if AES_vif;
uvm_active_passive_enum sel_mode;

`uvm_object_utils_begin(AES_config)
    `uvm_field_enum(uvm_active_passive_enum, sel_mode, UVM_DEFAULT)
`uvm_object_utils_end

function new (string name = "AES_config");
    super.new(name);
endfunction

endclass