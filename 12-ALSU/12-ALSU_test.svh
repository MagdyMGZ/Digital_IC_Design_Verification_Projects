class ALSU_test extends uvm_test;
    `uvm_component_utils(ALSU_test)

   ALSU_env env_alsu;
   shift_reg_env env_shift_reg;
   ALSU_config_obj config_obj_alsu;
   shift_reg_config_obj config_obj_shift_reg;
   ALSU_main_sequence main_seq;
   ALSU_reset_sequence reset_seq;
   direct_test_sequence seq_directed;

    function new (string name ="ALSU_test", uvm_component parent = null);
        super.new(name,parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        env_alsu = ALSU_env::type_id::create("env_alsu",this);
        env_shift_reg = shift_reg_env::type_id::create("env_shift_reg",this);
        config_obj_alsu = ALSU_config_obj::type_id::create ("config_obj_alsu");
        config_obj_shift_reg = shift_reg_config_obj::type_id::create ("config_obj_shift_reg");
        main_seq = ALSU_main_sequence::type_id::create("main_seq");
        reset_seq = ALSU_reset_sequence::type_id::create("reset_seq");
        seq_directed = direct_test_sequence::type_id::create("seq_directed");
        if(!uvm_config_db #(virtual ALSU_if)::get(this,"","ALSU_if",config_obj_alsu.alsu_vif))begin
            `uvm_fatal("build_phase","the test unable to get the virtual interface");
        end
        if(!uvm_config_db #(virtual shift_reg_if)::get(this,"","shift_reg_if",config_obj_shift_reg.shift_reg_vif))begin
            `uvm_fatal("build_phase","the test unable to get the virtual interface");
        end
        config_obj_alsu.sel_mod = UVM_ACTIVE;
        config_obj_shift_reg.sel_mod = UVM_PASSIVE;
        uvm_config_db #(ALSU_config_obj) :: set (this,"*","CGO",config_obj_alsu);
        uvm_config_db #(shift_reg_config_obj) :: set (this,"*","CGO",config_obj_shift_reg);
    endfunction

    task run_phase (uvm_phase phase);
        super .run_phase (phase);
        phase .raise_objection(this);
        //reset sequence
        `uvm_info("run_phase","reset asserted",UVM_LOW);
        reset_seq.start(env_alsu.agt.sqr);
        `uvm_info("run_phase","reset deasserted",UVM_LOW);

        //main sequence
        `uvm_info("run_phase","stimulus generated started",UVM_LOW);
        main_seq.start(env_alsu.agt.sqr);
        `uvm_info("run_phase","stimulus generated ended",UVM_LOW);

        //direct test sequence
        `uvm_info("run_phase","stimulus generated started",UVM_LOW);
        seq_directed.start(env_alsu.agt.sqr);    
        `uvm_info("run_phase","stimulus generated ended",UVM_LOW);
  
        phase .drop_objection(this);
    endtask 

endclass 
