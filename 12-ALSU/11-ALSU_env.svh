class ALSU_env extends uvm_env;
    `uvm_component_utils(ALSU_env);
    ALSU_agent agt;
    ALSU_scoreboard sb;
    ALSU_coverage cov;

    function new(string name ="shift_env",uvm_component parent = null);
        super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        agt = ALSU_agent::type_id::create("agt",this);
        sb = ALSU_scoreboard::type_id::create("sb",this);
        cov = ALSU_coverage::type_id::create("cov",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agt.agt_ap.connect(sb.sb_export);
        agt.agt_ap.connect (cov.cov_export);
    endfunction

endclass