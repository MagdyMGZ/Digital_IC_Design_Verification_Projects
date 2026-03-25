class AHB5_scoreboard extends uvm_scoreboard;

`uvm_component_utils(AHB5_scoreboard)

uvm_analysis_export #(AHB5_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(AHB5_sequence_item) sb_fifo;

AHB5_sequence_item AHB5_seq_item;

bit                    HRESP_REF;
bit                    HREADYOUT_REF;
bit [DATA_WIDTH-1:0]   HRDATA_REF;

bit                    HSELx_FF;
bit                    HREADY_FF;
bit [ADDR_WIDTH-1:0]   HADDR_FF;
bit [HBURST_WIDTH-1:0] HBURST_FF;
bit [2:0]              HSIZE_FF;
bit [1:0]              HTRANS_FF;
bit [DATA_WIDTH-1:0]   HWDATA_FF;
bit                    HWRITE_FF;
bit [STRB_WIDTH-1:0]   HWSTRB_FF;

bit [DATA_WIDTH-1:0] data_memory [MEM_DEPTH];
bit [OFFSET-1:0] offset;
bit [DATA_WIDTH-1:0] mask;
bit [DATA_WIDTH-1:0] HWDATA_mask;

bit invalid_trans;

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
        if ((AHB5_seq_item.HRDATA === HRDATA_REF) && (AHB5_seq_item.HREADYOUT === HREADYOUT_REF) && (AHB5_seq_item.HRESP === HRESP_REF)) begin
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

task pipeline_registers (input AHB5_sequence_item seq_item_gold);
    if (!seq_item_gold.HRESETn) begin
        HSELx_FF  <= 0;
        HREADY_FF <= 0;
        HADDR_FF  <= 0;
        HBURST_FF <= 0;
        HSIZE_FF  <= 0;
        HTRANS_FF <= 0;
        HWDATA_FF <= 0;
        HWRITE_FF <= 0;
        HWSTRB_FF <= 0;
    end
    else begin
        HSELx_FF  <= seq_item_gold.HSELx;
        HREADY_FF <= seq_item_gold.HREADY;
        HADDR_FF  <= seq_item_gold.HADDR;
        HBURST_FF <= seq_item_gold.HBURST;
        HSIZE_FF  <= seq_item_gold.HSIZE;
        HTRANS_FF <= seq_item_gold.HTRANS;
        HWDATA_FF <= seq_item_gold.HWDATA;
        HWRITE_FF <= seq_item_gold.HWRITE;
        HWSTRB_FF <= seq_item_gold.HWSTRB;
    end
endtask

function void reference_model(input AHB5_sequence_item seq_item_gold);
    pipeline_registers(seq_item_gold);
    offset = HADDR_FF[OFFSET-1:0];
    invalid_trans = ((offset > (MEM_DEPTH-1)) || ((8 << HSIZE_FF) > DATA_WIDTH));
    mask = {{8{HWSTRB_FF[3]}},{8{HWSTRB_FF[2]}},{8{HWSTRB_FF[1]}},{8{HWSTRB_FF[0]}}};
    HWDATA_mask = ((HWDATA_FF & mask) | (data_memory[offset] & ~mask));
    if (!seq_item_gold.HRESETn) begin
        HRESP_REF = 0;
        HREADYOUT_REF = 0;
        HRDATA_REF = 0;
    end
    else begin
        if (HREADY_FF && HSELx_FF) begin
            if (invalid_trans) begin
                HRESP_REF = 1;    
                HREADYOUT_REF = 1;  
            end
            else begin
                HRESP_REF = 0; 
                if ((HTRANS_FF == 2'b10) || (HTRANS_FF == 2'b11)) begin 
                    HREADYOUT_REF = 1;                                  
                    if (HWRITE_FF) begin                             
                        case ({offset[1:0],HSIZE_FF})
                            5'b00_000 : data_memory[offset] = HWDATA_mask[7:0]; 
                            5'b00_001 : data_memory[offset] = HWDATA_mask[15:0];   
                            5'b00_010 : data_memory[offset] = HWDATA_mask;         
                            5'b01_000 : data_memory[offset] = HWDATA_mask[15:8];   
                            5'b10_000 : data_memory[offset] = HWDATA_mask[23:16];  
                            5'b10_001 : data_memory[offset] = HWDATA_mask[31:16];  
                            5'b11_000 : data_memory[offset] = HWDATA_mask[31:24];  
                            default   : data_memory[offset] = HWDATA_mask;      
                        endcase
                    end
                    else begin    
                        case ({offset[1:0],HSIZE_FF})
                            5'b00_000 : HRDATA_REF = data_memory[offset][7:0];  
                            5'b00_001 : HRDATA_REF = data_memory[offset][15:0]; 
                            5'b00_010 : HRDATA_REF = data_memory[offset];     
                            5'b01_000 : HRDATA_REF = data_memory[offset][15:8];   
                            5'b10_000 : HRDATA_REF = data_memory[offset][23:16]; 
                            5'b10_001 : HRDATA_REF = data_memory[offset][31:16];   
                            5'b11_000 : HRDATA_REF = data_memory[offset][31:24];  
                            default   : HRDATA_REF = data_memory[offset];  
                        endcase
                    end
                end
                else begin          
                    HREADYOUT_REF = 0;  
                end
            end
        end
        else begin    
            HRESP_REF = 0;   
            HREADYOUT_REF = 0; 
        end 
    end
endfunction 

endclass