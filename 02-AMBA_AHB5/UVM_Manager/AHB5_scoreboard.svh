class AHB5_scoreboard extends uvm_scoreboard;

`uvm_component_utils(AHB5_scoreboard)

uvm_analysis_export #(AHB5_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(AHB5_sequence_item) sb_fifo;

AHB5_sequence_item AHB5_seq_item;

logic                  HRESP_REF;
logic                  HREADYOUT_REF;
logic [DATA_WIDTH-1:0] HRDATA_REF;

logic [7:0] MEM [MEM_DEPTH-1:0];
logic [DATA_WIDTH-1:0] mask;
logic [OFFSET-1:0] address;

int error_count, correct_count;
int unsigned transaction_counter_mon;
int unsigned transaction_counter_sb;
bit check_state;

function new (string name = "AHB5_scoreboard", uvm_component parent = null);
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
        sb_fifo.get(AHB5_seq_item);
        transaction_counter_sb++;
        reference_model(AHB5_seq_item);
        if ((AHB5_seq_item.HRDATA === HRDATA_REF) || (AHB5_seq_item.HREADYOUT === HREADYOUT_REF) || (AHB5_seq_item.HRESP === HRESP_REF)) begin
            `uvm_info("run_phase",$sformatf("Correct AHB5 Outputs : %s",AHB5_seq_item.convert2string()),UVM_DEBUG);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (HREADYOUT = %0d) , doesn't Match with the Golden model output (HREADYOUT_REF = %0d)",AHB5_seq_item.HREADYOUT,HREADYOUT_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (HRDATA = %0d) , doesn't Match with the Golden model output (HRDATA_REF = %0d)",AHB5_seq_item.HRDATA,HRDATA_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (HRESP = %0d) , doesn't Match with the Golden model output (HRESP_REF = %0d)",AHB5_seq_item.HRESP,HRESP_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s",AHB5_seq_item.convert2string()));
            error_count++;
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
    if (transaction_counter_mon < TESTS) begin
        wait(transaction_counter_sb == TESTS);
        check_state = 1'b1;
    end
endtask

function void reference_model(input AHB5_sequence_item seq_item_gold);
    if (!seq_item_gold.HRESETn) begin
        HRESP_REF = 0;
        HREADYOUT_REF = 0;
        HRDATA_REF = 0;
    end
    else begin
        HRESP_REF = 0;
        if (seq_item_gold.HREADY && seq_item_gold.HSEL1 && !HRESP_REF) begin
            address = seq_item_gold.HADDR[OFFSET-1:0];
            mask = {{8{seq_item_gold.HWSTRB[3]}},{8{seq_item_gold.HWSTRB[2]}},{8{seq_item_gold.HWSTRB[1]}},{8{seq_item_gold.HWSTRB[0]}}};
            if ((seq_item_gold.HTRANS == NONSEQ) || (seq_item_gold.HTRANS == SEQ)) begin
                HREADYOUT_REF = 1;
                if (seq_item_gold.HWRITE) begin
                    case (seq_item_gold.HSIZE)
                        BYTE : begin
                            MEM[address+0] = ((seq_item_gold.HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                        end
                        HALFWORD : begin
                            MEM[address+0] = ((seq_item_gold.HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] = ((seq_item_gold.HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                        end
                        WORD : begin
                            MEM[address+0] = ((seq_item_gold.HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] = ((seq_item_gold.HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] = ((seq_item_gold.HWDATA[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] = ((seq_item_gold.HWDATA[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end 
                        default : begin
                            MEM[address+0] = ((seq_item_gold.HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] = ((seq_item_gold.HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] = ((seq_item_gold.HWDATA[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] = ((seq_item_gold.HWDATA[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end
                    endcase
                end
                else begin
                    case (seq_item_gold.HSIZE)
                        BYTE     : HRDATA_REF = {24'b0,MEM[address+0]};
                        HALFWORD : HRDATA_REF = {16'b0,MEM[address+1],MEM[address+0]};
                        WORD     : HRDATA_REF = {MEM[address+3],MEM[address+2],MEM[address+1],MEM[address+0]};
                        default  : HRDATA_REF = {MEM[address+3],MEM[address+2],MEM[address+1],MEM[address+0]};
                    endcase
                end
            end
            else begin
                HREADYOUT_REF = 0;
                HRDATA_REF = 0;
            end
        end
        else begin
            HREADYOUT_REF = 0;
            HRDATA_REF = 0;
        end
    end
endfunction 

endclass