class ASYNCH_FIFO_env extends uvm_env;

`uvm_component_utils(ASYNCH_FIFO_env)

ASYNCH_FIFO_agent agt;
ASYNCH_FIFO_scoreboard sb;
ASYNCH_FIFO_collector cov;

function new (string name = "ASYNCH_FIFO_env", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    agt = ASYNCH_FIFO_agent::type_id::create("agt",this);
    sb = ASYNCH_FIFO_scoreboard::type_id::create("sb",this);
    cov = ASYNCH_FIFO_collector::type_id::create("cov",this);    
endfunction

function void connect_phase (uvm_phase phase);
    agt.agt_ap.connect(sb.sb_export);
    agt.agt_ap.connect(cov.cov_export);
endfunction

endclass