class ALSU_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(ALSU_scoreboard);

    uvm_analysis_export #(ALSU_seq_item) sb_export;
    uvm_tlm_analysis_fifo #(ALSU_seq_item) sb_fifo;
    ALSU_seq_item seq_item_sb;

    int error_count;
    int correct_count;

    function new(string name ="ALSU_scoreboard",uvm_component parent = null);
            super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        sb_export = new("sb_export",this);
        sb_fifo = new("sb_fifo",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        sb_export.connect(sb_fifo.analysis_export);
    endfunction

    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        forever begin
            sb_fifo.get(seq_item_sb);
            if (seq_item_sb.out !== seq_item_sb.out_G) begin
                `uvm_error("run_phase",$sformatf("comparison failed,transaction recieved by the DUT:%s",seq_item_sb.convert2string()));     
                error_count++;
            end
            else begin
                `uvm_info("run_phase",$sformatf("correct out_refput :%s ",seq_item_sb.convert2string()),UVM_HIGH);     
                correct_count++; 
            end
        end
    endtask

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("report_phase",$sformatf("Total successful counts : %0d",correct_count),UVM_MEDIUM);     
        `uvm_info("report_phase",$sformatf("Total failed counts : %0d",error_count),UVM_MEDIUM);     
    endfunction

endclass