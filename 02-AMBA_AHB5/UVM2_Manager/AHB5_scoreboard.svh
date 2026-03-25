class AHB5_scoreboard extends uvm_scoreboard;

`uvm_component_utils(AHB5_scoreboard)

uvm_analysis_export #(AHB5_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(AHB5_sequence_item) sb_fifo;

AHB5_sequence_item AHB5_seq_item;

logic                  HRESP_REF;
logic                  HREADYOUT_REF;
logic [DATA_WIDTH-1:0] HRDATA_REF;

logic                  HSELx_FF;
logic                  HREADY_FF;
logic [ADDR_WIDTH-1:0] HADDR_FF;
hburst_e               HBURST_FF;
hsize_e                HSIZE_FF;
logic [DATA_WIDTH-1:0] HWDATA_FF;
type_e                 HWRITE_FF;
htrans_e               HTRANS_FF;
logic [STRB_WIDTH-1:0] HWSTRB_FF;
int                    write_index;

logic [DATA_WIDTH-1:0] data_memory [MEM_DEPTH];

logic                  invalid_trans;
logic [OFFSET-1:0]     data_mem_offset;
logic [DATA_WIDTH-1:0] mask;
logic [DATA_WIDTH-1:0] HWDATA_mask;

int error_count, correct_count;

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
        reference_model(AHB5_seq_item);
        if ((AHB5_seq_item.rdata === HRDATA_REF) && (AHB5_seq_item.valid === HREADYOUT_REF) && (AHB5_seq_item.trans_error === HRESP_REF)) begin
            `uvm_info("run_phase",$sformatf("Correct AHB5 Outputs : %s",AHB5_seq_item.convert2string()),UVM_DEBUG);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (valid = %0d) , doesn't Match with the Golden model output (HREADYOUT_REF = %0d)",AHB5_seq_item.valid,HREADYOUT_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (rdata = %0d) , doesn't Match with the Golden model output (HRDATA_REF = %0d)",AHB5_seq_item.rdata,HRDATA_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (trans_error = %0d) , doesn't Match with the Golden model output (HRESP_REF = %0d)",AHB5_seq_item.trans_error,HRESP_REF));
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

task pipeline_registers (input AHB5_sequence_item seq_item_gold);
    if (!seq_item_gold.rst_n) begin
        HSELx_FF  <= 0;
        HREADY_FF <= 0;
        HADDR_FF  <= 0;
        HBURST_FF <= hburst_e'(0);
        HSIZE_FF  <= hsize_e'(0);
        HWDATA_FF <= 0;
        HTRANS_FF <= htrans_e'(0);
        HWRITE_FF <= type_e'(0);
        HWSTRB_FF <= 0;
    end
    else begin
        HSELx_FF  <= seq_item_gold.slv_sel;
        HREADY_FF <= seq_item_gold.slv_enable;
        HADDR_FF  <= seq_item_gold.address;
        HBURST_FF <= seq_item_gold.burst;
        HSIZE_FF  <= seq_item_gold.size;
        HWDATA_FF <= seq_item_gold.wdata_arr[write_index];
        HTRANS_FF <= (!seq_item_gold.rst_n || !seq_item_gold.slv_sel)? IDLE : (!seq_item_gold.slv_enable)? BUSY : (write_index == 0)? NONSEQ : SEQ;
        HWRITE_FF <= seq_item_gold.write;
        HWSTRB_FF <= seq_item_gold.strb;
    end
endtask

function void reference_model(input AHB5_sequence_item seq_item_gold);
    pipeline_registers(seq_item_gold);
    data_mem_offset = HADDR_FF[OFFSET-1:0];
    invalid_trans = ((data_mem_offset > (MEM_DEPTH-1)) || ((8 << HSIZE_FF) > DATA_WIDTH));
    mask = ({{8{HWSTRB_FF[3]}},{8{HWSTRB_FF[2]}},{8{HWSTRB_FF[1]}},{8{HWSTRB_FF[0]}}});
    HWDATA_mask = ((HWDATA_FF & mask) | (data_memory[data_mem_offset] & ~mask));
    ////////////////////////////////////////
    if (!seq_item_gold.rst_n) begin
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
                if ((HTRANS_FF == NONSEQ) || (HTRANS_FF == SEQ)) begin
                    HREADYOUT_REF = 1;                                     
                    if (HWRITE_FF) begin                                                    
                        case ({data_mem_offset[1:0],HSIZE_FF})
                            5'b00_000 : data_memory[data_mem_offset] = HWDATA_mask[7:0];   
                            5'b00_001 : data_memory[data_mem_offset] = HWDATA_mask[15:0];  
                            5'b00_010 : data_memory[data_mem_offset] = HWDATA_mask;     
                            5'b01_000 : data_memory[data_mem_offset] = HWDATA_mask[15:8];  
                            5'b10_000 : data_memory[data_mem_offset] = HWDATA_mask[23:16];  
                            5'b10_001 : data_memory[data_mem_offset] = HWDATA_mask[31:16];
                            5'b11_000 : data_memory[data_mem_offset] = HWDATA_mask[31:24]; 
                            default   : data_memory[data_mem_offset] = HWDATA_mask;   
                        endcase
                    end
                    else begin        
                        case ({data_mem_offset[1:0],HSIZE_FF})
                            5'b00_000 : HRDATA_REF = data_memory[data_mem_offset][7:0]; 
                            5'b00_001 : HRDATA_REF = data_memory[data_mem_offset][15:0];  
                            5'b00_010 : HRDATA_REF = data_memory[data_mem_offset];      
                            5'b01_000 : HRDATA_REF = data_memory[data_mem_offset][15:8];  
                            5'b10_000 : HRDATA_REF = data_memory[data_mem_offset][23:16];
                            5'b10_001 : HRDATA_REF = data_memory[data_mem_offset][31:16]; 
                            5'b11_000 : HRDATA_REF = data_memory[data_mem_offset][31:24];
                            default   : HRDATA_REF = data_memory[data_mem_offset];       
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