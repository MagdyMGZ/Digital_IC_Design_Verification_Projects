class temp_env extends uvm_env;

`uvm_component_utils(temp_env)

temp_agent agt;
temp_scoreboard sb;
temp_collector cov;

function new (string name = "temp_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = temp_agent::type_id::create("agt",this);
    sb = temp_scoreboard::type_id::create("sb",this);
    cov = temp_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
endfunction

endclass