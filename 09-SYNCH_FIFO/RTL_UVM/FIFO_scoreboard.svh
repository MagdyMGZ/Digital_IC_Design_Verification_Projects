class FIFO_scoreboard extends uvm_scoreboard;

`uvm_component_utils(FIFO_scoreboard)

uvm_analysis_export #(FIFO_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(FIFO_sequence_item) sb_fifo;

FIFO_sequence_item FIFO_seq_item;

// Outputs Declaration
logic [FIFO_WIDTH-1:0] data_out_ref;
logic full_ref, almostfull_ref, empty_ref, almostempty_ref, overflow_ref, underflow_ref, wr_ack_ref;
int counter;                      // declared counter to count no. of elements in the queue 
logic [FIFO_WIDTH-1:0] queue [$];    // declared queue to check the FIFO 
logic [6:0] flags_ref, flags_dut;

int error_count, correct_count;
bit check_state;

function new (string name = "FIFO_scoreboard", uvm_component parent = null);
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
        sb_fifo.get(FIFO_seq_item);
        reference_model(FIFO_seq_item);
        flags_ref = {wr_ack_ref, overflow_ref, full_ref, empty_ref, almostfull_ref, almostempty_ref, underflow_ref};  // concatenated reference flags
        flags_dut = {FIFO_seq_item.wr_ack, FIFO_seq_item.overflow, FIFO_seq_item.full, FIFO_seq_item.empty, FIFO_seq_item.almostfull, FIFO_seq_item.almostempty, FIFO_seq_item.underflow};  // concatenated flags from the FIFO_seq_item.
        if ((FIFO_seq_item.data_out === data_out_ref) || (flags_dut === flags_ref)) begin
            `uvm_info("run_phase",$sformatf("Correct FIFO Outputs : %s",FIFO_seq_item.convert2string()),UVM_DEBUG);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (data_out = %0d) , doesn't Match with the Golden model output (data_out_ref = %0d)",FIFO_seq_item.data_out,data_out_ref));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (flags_dut = %0b) , doesn't Match with the Golden model output (flags_dut = %0b)",flags_dut,flags_dut));
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s",FIFO_seq_item.convert2string()));
            error_count++;
        end
    end
endtask

function void reference_model(input FIFO_sequence_item seq_item_gold);
    // Write Operation
    if (!seq_item_gold.rst_n) begin
        wr_ack_ref = 0;
        full_ref = 0;
        almostfull_ref = 0;
        overflow_ref = 0;
        queue.delete();	
    end
    else if (seq_item_gold.wr_en && (counter < FIFO_DEPTH)) begin  
        queue.push_back(seq_item_gold.data_in) ;
        wr_ack_ref = 1;
        overflow_ref = 0;
    end
    else begin 
        wr_ack_ref = 0; 
        if (full_ref && seq_item_gold.wr_en)
            overflow_ref = 1;
        else
            overflow_ref = 0;
    end

    // Read Operation
    if(!seq_item_gold.rst_n) begin
        empty_ref = 1;
        almostempty_ref = 0;
        underflow_ref = 0;
    end
    else if ( seq_item_gold.rd_en && counter != 0 ) begin   
        data_out_ref = queue.pop_front();
        underflow_ref = 0;
    end
    else begin
        if(empty_ref && seq_item_gold.rd_en)
            underflow_ref = 1;
        else
            underflow_ref = 0;
    end                

    // Counter Operation
    if(!seq_item_gold.rst_n)
        counter = 0;
    else if	( ({seq_item_gold.wr_en, seq_item_gold.rd_en} == 2'b10) && !full_ref) 
        counter = counter + 1;
    else if ( ({seq_item_gold.wr_en, seq_item_gold.rd_en} == 2'b01) && !empty_ref)
        counter = counter - 1;
    else if ( ({seq_item_gold.wr_en, seq_item_gold.rd_en} == 2'b11) && full_ref)
        counter = counter - 1;
    else if ( ({seq_item_gold.wr_en, seq_item_gold.rd_en} == 2'b11) && empty_ref)
        counter = counter + 1;

    // To get the updated values for the comb. flags
    full_ref = (counter == FIFO_DEPTH)? 1 : 0;     
    empty_ref = (counter == 0)? 1 : 0;
    almostfull_ref = (counter == FIFO_DEPTH-1)? 1 : 0;         
    almostempty_ref = (counter == 1)? 1 : 0;
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