class AES_test extends uvm_test;

`uvm_component_utils(AES_test)

AES_env env;           // Created using UVM 1.2
AES_config AES_cfg;    // Created using UVM 1.1d
AES_sequence AES_seq;  // Created using Normal Factory Registration 

uvm_factory factory1 = uvm_coreservice_t::get().get_factory();
uvm_factory factory2 = uvm_factory::get();

function new (string name = "AES_test", uvm_component parent = null);
    super.new(name,parent); 
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    $cast(env,factory1.create_component_by_type(AES_env::get_type(),get_full_name,"env",this));
    $cast(AES_cfg,factory2.create_object_by_name(AES_config::type_name,get_full_name,"AES_cfg"));
    AES_seq = AES_sequence::type_id::create("AES_seq");
    if (!uvm_config_db #(virtual AES_if)::get(this,"","AES_IF",AES_cfg.AES_vif))
        `uvm_fatal("build_phase","Test - Unable to get the virtual interface of the AES from the uvm_config_db");
    AES_cfg.sel_mode = UVM_ACTIVE;
    uvm_config_db #(AES_config)::set(this,"*","CFG",AES_cfg);
    factory1.set_type_override_by_type(AES_sequence_item_without_field_macros::get_type(),AES_sequence_item::get_type()); // OR
    factory1.set_type_override_by_name("AES_sequence_item_without_field_macros","AES_sequence_item");
    factory1.print();
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    `uvm_info("run_phase","Stimulus Generation Started",UVM_LOW)
    AES_seq.start(env.agt.sqr);
    `uvm_info("run_phase","Stimulus Generation Ended",UVM_LOW)

    AES_seq.record();

    phase.drop_objection(this);

    // phase.phase_done.set_drain_time(this, 20);
endtask

function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_config_db#(string)::dump();
    uvm_top.print_topology(); // Prints entire testbench hierarchy 
endfunction

function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    factory1.print(0);
    `uvm_info(get_full_name(), $sformatf("================================ End of %s ================================", this.get_type_name()), UVM_MEDIUM)
endfunction

virtual function void report_phase(uvm_phase phase);
    uvm_report_server svr;
    super.report_phase(phase);
    svr = uvm_report_server::get_server();
    if(svr.get_severity_count(UVM_FATAL)+svr.get_severity_count(UVM_ERROR)>0) begin
        `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
        `uvm_info(get_type_name(), "----            TEST FAIL          ----", UVM_NONE)
        `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
    end
    else begin
        `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
        `uvm_info(get_type_name(), "----           TEST PASS           ----", UVM_NONE)
        `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
    end
endfunction 

endclass