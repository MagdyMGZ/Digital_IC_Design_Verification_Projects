class AES_env extends uvm_env;

`uvm_component_utils(AES_env)

AES_agent agt;
AES_scoreboard sb;
AES_collector cov;

function new (string name = "AES_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = AES_agent::type_id::create("agt",this);
    sb = AES_scoreboard::type_id::create("sb",this);
    cov = AES_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
endfunction

endclass