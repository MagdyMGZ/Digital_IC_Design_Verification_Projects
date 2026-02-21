class temp_scoreboard extends uvm_scoreboard;

`uvm_component_utils(temp_scoreboard)

uvm_analysis_export #(temp_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(temp_sequence_item) sb_fifo;

temp_sequence_item temp_seq_item;

int error_count, correct_count;
int unsigned transaction_counter_sb;

// Reference Signals Declaration
logic Signals_REF;

function new (string name = "temp_scoreboard", uvm_component parent = null);
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
        sb_fifo.get(temp_seq_item);
        transaction_counter_sb++;
        reference_model(temp_seq_item);
        if (temp_seq_item.Signals === Signals_REF) begin
            `uvm_info("run_phase",$sformatf("Correct temp Outputs : %s",temp_seq_item.convert2string()),UVM_DEBUG);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (Signals = %0d) , doesn't Match with the Golden model output (Signals_REF = %0d)",temp_seq_item.Signals,Signals_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s",temp_seq_item.convert2string()));
            error_count++;
        end
    end
endtask

function void report_phase (uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("report_phase",$sformatf("SCOREBOARD %0d TRANSACTIONS",transaction_counter_sb),UVM_MEDIUM);
    `uvm_info("report_phase",$sformatf("Total Successful Counts : %0d",correct_count),UVM_MEDIUM);
    `uvm_info("report_phase",$sformatf("Total Failed Counts : %0d",error_count),UVM_MEDIUM);
endfunction

function void reference_model(temp_sequence_item seq_item_gold);
    // Signals_REF = ;
endfunction 

endclass