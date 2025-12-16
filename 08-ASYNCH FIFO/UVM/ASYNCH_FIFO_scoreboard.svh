class ASYNCH_FIFO_scoreboard extends uvm_scoreboard;

`uvm_component_utils(ASYNCH_FIFO_scoreboard)

uvm_analysis_export #(ASYNCH_FIFO_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(ASYNCH_FIFO_sequence_item) sb_fifo;

ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;

int error_count, correct_count;
bit check_state;

function new (string name = "ASYNCH_FIFO_scoreboard", uvm_component parent = null);
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
        sb_fifo.get(ASYNCH_FIFO_seq_item);
        if ((ASYNCH_FIFO_seq_item.o_rdata !== ASYNCH_FIFO_seq_item.o_rdata_gold) || (ASYNCH_FIFO_seq_item.o_full !== ASYNCH_FIFO_seq_item.o_full_gold) || (ASYNCH_FIFO_seq_item.o_empty !== ASYNCH_FIFO_seq_item.o_empty_gold)) begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (o_rdata = %0d) , doesn't Match with the Golden model output (o_rdata_ref = %0d)",ASYNCH_FIFO_seq_item.o_rdata, ASYNCH_FIFO_seq_item.o_rdata_gold));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (o_full = %0b) , doesn't Match with the Golden model output (o_full_ref = %0b)",ASYNCH_FIFO_seq_item.o_full, ASYNCH_FIFO_seq_item.o_full_gold));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (o_empty = %0b) , doesn't Match with the Golden model output (o_empty_ref = %0b)",ASYNCH_FIFO_seq_item.o_empty, ASYNCH_FIFO_seq_item.o_empty_gold));
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s",ASYNCH_FIFO_seq_item.convert2string()));
            error_count++;
        end
        else begin
            `uvm_info("run_phase",$sformatf("Correct ASYNCH_FIFO Outputs : %s",ASYNCH_FIFO_seq_item.convert2string()),UVM_FULL);
            correct_count++;
        end
    end
endtask

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