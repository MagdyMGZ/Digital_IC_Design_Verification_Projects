import "DPI-C" function void call_python_script();

class AES_scoreboard extends uvm_scoreboard;

`uvm_component_utils(AES_scoreboard)

uvm_analysis_export #(AES_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(AES_sequence_item) sb_fifo;

AES_sequence_item AES_seq_item, AES_seq_item_exp;

int error_count, correct_count;
int unsigned transaction_counter_mon;
int unsigned transaction_counter_sb;
bit check_state;

// refrence output
int           key_file;
int           output_file;
// logic [N-1:0] out_ref;
// string out_ref, out_dut;

function new (string name = "AES_scoreboard", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    AES_seq_item_exp = AES_sequence_item::type_id::create("AES_seq_item_exp");
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
        sb_fifo.get(AES_seq_item);
        reference_model(AES_seq_item);
        // COMPARE THE ACTUAL OUTPUT AND EXPECTED OUTPUT
        // if (AES_seq_item.out == out_ref) begin
        if (AES_seq_item_exp.compare(AES_seq_item)) begin
            `uvm_info("run_phase",$sformatf("Correct AES Outputs : %s",AES_seq_item.convert2string()),UVM_FULL);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s, doesn't Match with the Golden model output: %s",AES_seq_item.sprint(),AES_seq_item_exp.sprint()));
            error_count++;
        end
        transaction_counter_sb++;
    end
endtask

function void reference_model(input AES_sequence_item seq_item_gold);
    AES_seq_item_exp.copy(seq_item_gold);
    
    // Open file "key.txt" for writing
    key_file = $fopen("./key.txt","w");
    if (key_file == 0) begin
        $display("Error in key file opening");
    end 

    // Writing to file : First line writing the data , Second line writing the key
    $fdisplay(key_file,"%h \n%h",AES_seq_item_exp.in , AES_seq_item_exp.key);
    // $fwrite(key_file, "%h\n%h",seq_item_gold.in,seq_item_gold.key);

    // Close the "key.txt"
    $fclose(key_file);

    // "$system" task to run the python code and interact with SCOREBOARD through I/O files
    // $system($sformatf("python ../SIM/Golden_model.py"));
    call_python_script(); // Call C function

    // Open file "output.txt" for reading
    output_file = $fopen("./output.txt","r");

    // Reading the output of python code through "output.txt" file
    // $fscanf(output_file,"%h",out_ref);
    $fscanf(output_file,"%h",AES_seq_item_exp.out);
    // if (output_file) begin
    //     while (!$feof(output_file)) begin
    //         $fgets(out_ref, output_file); // Return out_ref in String
    //     end
    // end

    // Close the "output.txt"
    $fclose(output_file);

    // out_dut = $sformatf("%h",seq_item_gold.out); // make out_dut in String
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
    if (transaction_counter_mon < TESTS) begin
        wait(transaction_counter_sb == TESTS);
        check_state = 1'b1;
    end
endtask

endclass