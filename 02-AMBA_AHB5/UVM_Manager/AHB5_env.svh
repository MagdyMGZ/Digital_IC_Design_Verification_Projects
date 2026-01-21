class AHB5_env extends uvm_env;

`uvm_component_utils(AHB5_env)

AHB5_agent agt;
AHB5_scoreboard sb;
AHB5_collector cov;

function new (string name = "AHB5_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = AHB5_agent::type_id::create("agt",this);
    sb = AHB5_scoreboard::type_id::create("sb",this);
    cov = AHB5_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
    sb.transaction_counter_mon = agt.mon.transaction_counter_mon;
endfunction

endclass