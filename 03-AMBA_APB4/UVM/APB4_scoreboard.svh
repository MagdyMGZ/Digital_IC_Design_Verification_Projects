class APB4_scoreboard extends uvm_scoreboard;

`uvm_component_utils(APB4_scoreboard)

uvm_analysis_export #(APB4_sequence_item) sb_export;
uvm_tlm_analysis_fifo #(APB4_sequence_item) sb_fifo;

APB4_sequence_item APB4_seq_item;

logic                  READY_REF;
logic                  SLVERR_REF;
logic [DATA_WIDTH-1:0] RDATA_REF;

logic [DATA_WIDTH-1:0] MEM [MEM_DEPTH-1:0];
logic [DATA_WIDTH-1:0] mask;

logic [DATA_WIDTH-1:0] SYS_STATUS_REG;
logic [DATA_WIDTH-1:0] INT_CTRL_REG;
logic [DATA_WIDTH-1:0] DEV_ID_REG;
logic [DATA_WIDTH-1:0] MEM_CTRL_REG;
logic [DATA_WIDTH-1:0] TEMP_SENSOR_REG;
logic [DATA_WIDTH-1:0] ADC_CTRL_REG;
logic [DATA_WIDTH-1:0] DBG_CTRL_REG;
logic [DATA_WIDTH-1:0] GPIO_DATA_REG;
logic [DATA_WIDTH-1:0] DAC_OUTPUT_REG;
logic [DATA_WIDTH-1:0] VOLTAGE_CTRL_REG;
logic [DATA_WIDTH-1:0] CLK_CONFIG_REG;
logic [DATA_WIDTH-1:0] TIMER_COUNT_REG;
logic [DATA_WIDTH-1:0] INPUT_DATA_REG;
logic [DATA_WIDTH-1:0] OUTPUT_DATA_REG;
logic [DATA_WIDTH-1:0] DMA_CTRL_REG;
logic [DATA_WIDTH-1:0] SYS_CTRL_REG;

int error_count, correct_count;
int unsigned transaction_counter_mon;
int unsigned transaction_counter_sb;
bit check_state;

function new (string name = "APB4_scoreboard", uvm_component parent = null);
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
        sb_fifo.get(APB4_seq_item);
        transaction_counter_sb++;
        reference_model(APB4_seq_item);
        if ((APB4_seq_item.READY === READY_REF) || (APB4_seq_item.RDATA === RDATA_REF) || (APB4_seq_item.SLVERR === SLVERR_REF)) begin
            `uvm_info("run_phase",$sformatf("Correct APB4 Outputs : %s",APB4_seq_item.convert2string()),UVM_DEBUG);
            correct_count++;
        end
        else begin
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (READY = %0d) , doesn't Match with the Golden model output (READY_REF = %0d)",APB4_seq_item.READY,READY_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (RDATA = %0d) , doesn't Match with the Golden model output (RDATA_REF = %0d)",APB4_seq_item.RDATA,RDATA_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, the output of the DUT (SLVERR = %0d) , doesn't Match with the Golden model output (SLVERR_REF = %0d)",APB4_seq_item.SLVERR,SLVERR_REF));
            `uvm_error("run_phase",$sformatf("Comparison failed, Transaction recieved by the DUT: %s",APB4_seq_item.convert2string()));
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

function void reference_model(input APB4_sequence_item seq_item_gold);
    case(seq_item_gold.slave)
        1'b0 : begin
            if (!seq_item_gold.PRESETn) begin
                READY_REF  = 0;
                RDATA_REF  = 0;
                SLVERR_REF = 0;
                mask = 0;
            end
            else begin
                if (seq_item_gold.TRANSFER) begin
                    READY_REF = 1;
                    SLVERR_REF = 0;
                    mask = {{8{seq_item_gold.STRB[3]}},{8{seq_item_gold.STRB[2]}},{8{seq_item_gold.STRB[1]}},{8{seq_item_gold.STRB[0]}}};
                    if (seq_item_gold.WRITE) begin
                        case (seq_item_gold.ADDR)
                            32'h0000_0000: SYS_STATUS_REG	= (SYS_STATUS_REG   &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0004: INT_CTRL_REG		= (INT_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0008: DEV_ID_REG		= (DEV_ID_REG       &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_000c: MEM_CTRL_REG		= (MEM_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0010: TEMP_SENSOR_REG	= (TEMP_SENSOR_REG  &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0014: ADC_CTRL_REG		= (ADC_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0018: DBG_CTRL_REG		= (DBG_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_001c: GPIO_DATA_REG	= (GPIO_DATA_REG    &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0020: DAC_OUTPUT_REG	= (DAC_OUTPUT_REG   &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0024: VOLTAGE_CTRL_REG	= (VOLTAGE_CTRL_REG &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0028: CLK_CONFIG_REG	= (CLK_CONFIG_REG   &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_002c: TIMER_COUNT_REG	= (TIMER_COUNT_REG  &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0030: INPUT_DATA_REG	= (INPUT_DATA_REG   &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0034: OUTPUT_DATA_REG	= (OUTPUT_DATA_REG  &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_0038: DMA_CTRL_REG		= (DMA_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                            32'h0000_003c: SYS_CTRL_REG		= (SYS_CTRL_REG     &	~mask) | (seq_item_gold.WDATA & mask);
                        endcase
                    end
                    else begin
                        case (seq_item_gold.ADDR)
                            32'h0000_0000: RDATA_REF = SYS_STATUS_REG;
                            32'h0000_0004: RDATA_REF = INT_CTRL_REG;
                            32'h0000_0008: RDATA_REF = DEV_ID_REG;
                            32'h0000_000c: RDATA_REF = MEM_CTRL_REG;
                            32'h0000_0010: RDATA_REF = TEMP_SENSOR_REG;
                            32'h0000_0014: RDATA_REF = ADC_CTRL_REG;
                            32'h0000_0018: RDATA_REF = DBG_CTRL_REG;
                            32'h0000_001c: RDATA_REF = GPIO_DATA_REG;
                            32'h0000_0020: RDATA_REF = DAC_OUTPUT_REG;
                            32'h0000_0024: RDATA_REF = VOLTAGE_CTRL_REG;
                            32'h0000_0028: RDATA_REF = CLK_CONFIG_REG;
                            32'h0000_002c: RDATA_REF = TIMER_COUNT_REG;
                            32'h0000_0030: RDATA_REF = INPUT_DATA_REG;
                            32'h0000_0034: RDATA_REF = OUTPUT_DATA_REG;
                            32'h0000_0038: RDATA_REF = DMA_CTRL_REG;
                            32'h0000_003c: RDATA_REF = SYS_CTRL_REG;
                        endcase
                    end
                end
                else begin
                    READY_REF  = 0;
                    RDATA_REF  = 0;
                    SLVERR_REF = 0;
                    mask = 0;
                end
            end
        end
        1'b1 : begin
            if (!seq_item_gold.PRESETn) begin
                READY_REF  = 0;
                RDATA_REF  = 0;
                SLVERR_REF = 0;
                mask = 0;
            end
            else begin
                if (seq_item_gold.TRANSFER) begin
                    READY_REF = 1;
                    SLVERR_REF = 0;
                    mask = {{8{seq_item_gold.STRB[3]}},{8{seq_item_gold.STRB[2]}},{8{seq_item_gold.STRB[1]}},{8{seq_item_gold.STRB[0]}}};
                    if (seq_item_gold.WRITE) begin
                        MEM[seq_item_gold.ADDR[$clog2(MEM_DEPTH)-1:0]] = (MEM[seq_item_gold.ADDR[$clog2(MEM_DEPTH)-1:0]] & ~mask) | (seq_item_gold.WDATA & mask);
                    end
                    else begin
                        RDATA_REF = MEM[seq_item_gold.ADDR[$clog2(MEM_DEPTH)-1:0]];
                    end
                end
                else begin
                    READY_REF  = 0;
                    RDATA_REF  = 0;
                    SLVERR_REF = 0;
                    mask = 0;
                end
            end
        end
        default : begin
            READY_REF  = 0;
            RDATA_REF  = 0;
            SLVERR_REF = 0;
            mask = 0;
        end
    endcase
endfunction 

endclass