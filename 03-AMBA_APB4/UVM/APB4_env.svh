class APB4_env extends uvm_env;

`uvm_component_utils(APB4_env)

APB4_agent agt;
APB4_scoreboard sb;
APB4_collector cov;

function new (string name = "APB4_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = APB4_agent::type_id::create("agt",this);
    sb = APB4_scoreboard::type_id::create("sb",this);
    cov = APB4_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
    sb.transaction_counter_mon = agt.mon.transaction_counter_mon;
endfunction

endclass