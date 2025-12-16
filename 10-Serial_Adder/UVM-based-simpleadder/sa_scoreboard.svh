class sa_scoreboard extends uvm_scoreboard;

`uvm_component_utils(sa_scoreboard)

uvm_analysis_export #(sa_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(sa_sequence_item) sb_fifo;

sa_sequence_item sa_seq_item;

bit [2:0] sa_ref;
int error_count, correct_count;
bit check_state;

function new (string name = "sa_scoreboard", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    sb_export = new("sb_export",this);
    sb_fifo = new("sb_fifo",this);
endfunction

function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    sb_export.connect(sb_fifo.analysis_export);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        sb_fifo.get(sa_seq_item);
        ref_model(sa_seq_item);
        if (sa_seq_item.out !== sa_ref) begin
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s while the reference out = %0d",sa_seq_item.convert2string(),sa_ref));
            error_count++;
        end
        else begin
            `uvm_info("run_phase",$sformatf("Correct sa_out : %s",sa_seq_item.convert2string()),UVM_FULL);
            correct_count++;
        end
    end
endtask

function void ref_model (sa_sequence_item sa_seq_item);
    sa_ref = sa_seq_item.a + sa_seq_item.b;
endfunction

function void report_phase (uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("report_phase",$sformatf("Total Successful Counts : %0d",correct_count),UVM_MEDIUM);
    `uvm_info("report_phase",$sformatf("Total Failed Counts : %0d",error_count),UVM_MEDIUM);
endfunction


virtual function void phase_ready_to_end (uvm_phase phase);
    if (phase.is(uvm_run_phase::get())) begin
        if (!check_state == 1'b1) begin
            phase.raise_objection(this,"Test Not Yet Ready to End");
            fork
                begin
                    `uvm_info("PRTE","Phase Ready Testing",UVM_LOW)
                    wait_for_ok_to_finish();
                    phase.drop_objection(this,"Test Ready to End");
                end
            join_none
        end
    end
endfunction

task wait_for_ok_to_finish ();
    #50; // Could be any Logic Here
    if (correct_count == TESTS)
        check_state = 1'b1;
endtask


endclass