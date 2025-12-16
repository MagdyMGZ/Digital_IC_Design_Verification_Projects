package wrapper_config_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    class wrapper_config extends uvm_object;
        `uvm_object_utils(wrapper_config)
        virtual wrapper_if wrapper_vif;
        uvm_active_passive_enum wrapper_mode;
        function new(string name = "wrapper_config");
            super.new(name);
        endfunction
    endclass
endpackage

