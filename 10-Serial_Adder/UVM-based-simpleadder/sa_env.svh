class sa_env extends uvm_env;

`uvm_component_utils(sa_env)

sa_agent agt;
sa_scoreboard sb;
sa_collector cov;

function new (string name = "sa_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = sa_agent::type_id::create("agt",this);
    sb = sa_scoreboard::type_id::create("sb",this);
    cov = sa_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
endfunction

endclass