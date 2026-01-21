////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : APB4_REGFILE_SLV0.v 
////////////////////////////////////////////////////////////////////////////////
module APB4_REGFILE_SLV0 #(
    parameter  DATA_WIDTH = 32,
    parameter  ADDR_WIDTH = 32,
    localparam STRB_WIDTH = DATA_WIDTH/8
) (
    input       wire                                PCLK,
    input       wire                                PRESETn,
    input       wire        [ADDR_WIDTH-1:0]        PADDR,
    input       wire                                PSEL0,
    input       wire                                PENABLE,
    input       wire                                PWRITE,
    input       wire        [DATA_WIDTH-1:0]        PWDATA,
    input       wire        [STRB_WIDTH-1:0]        PSTRB,
    output      reg                                 PREADY,
    output      reg         [DATA_WIDTH-1:0]        PRDATA,
    output      reg                                 PSLVERR
);

reg [DATA_WIDTH-1:0] SYS_STATUS_REG;
reg [DATA_WIDTH-1:0] INT_CTRL_REG;
reg [DATA_WIDTH-1:0] DEV_ID_REG;
reg [DATA_WIDTH-1:0] MEM_CTRL_REG;
reg [DATA_WIDTH-1:0] TEMP_SENSOR_REG;
reg [DATA_WIDTH-1:0] ADC_CTRL_REG;
reg [DATA_WIDTH-1:0] DBG_CTRL_REG;
reg [DATA_WIDTH-1:0] GPIO_DATA_REG;
reg [DATA_WIDTH-1:0] DAC_OUTPUT_REG;
reg [DATA_WIDTH-1:0] VOLTAGE_CTRL_REG;
reg [DATA_WIDTH-1:0] CLK_CONFIG_REG;
reg [DATA_WIDTH-1:0] TIMER_COUNT_REG;
reg [DATA_WIDTH-1:0] INPUT_DATA_REG;
reg [DATA_WIDTH-1:0] OUTPUT_DATA_REG;
reg [DATA_WIDTH-1:0] DMA_CTRL_REG;
reg [DATA_WIDTH-1:0] SYS_CTRL_REG;

wire [DATA_WIDTH-1:0] mask;
wire [ADDR_WIDTH-1:0] reg_addr;

assign reg_addr = (PSEL0 && PENABLE)? {8'h00, PADDR[23:0]} : 0;

genvar  i;
generate
    for (i = 0 ; i < STRB_WIDTH ; i = i + 1) begin
        assign mask[i*8 +: 8] = {8{PSTRB[i]}};
    end
endgenerate

always @(*) begin
    if (PSEL0 && PENABLE) begin
        if ((reg_addr % 4) != 0)
            PSLVERR = 1;
        else
            PSLVERR = 0;
    end
    else begin
        PSLVERR = 0;
    end
end

always @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
        PREADY <= 0;
        PRDATA <= 0;
    end
    else begin
        if (PSEL0 && PENABLE && ~PSLVERR) begin
            PREADY <= 1;
            if (PWRITE) begin
                case (reg_addr)
                    32'h0000_0000: SYS_STATUS_REG	<= (SYS_STATUS_REG   &	~mask) | (PWDATA & mask);
                    32'h0000_0004: INT_CTRL_REG		<= (INT_CTRL_REG     &	~mask) | (PWDATA & mask);
                    32'h0000_0008: DEV_ID_REG		<= (DEV_ID_REG       &	~mask) | (PWDATA & mask);
                    32'h0000_000c: MEM_CTRL_REG		<= (MEM_CTRL_REG     &	~mask) | (PWDATA & mask);
                    32'h0000_0010: TEMP_SENSOR_REG	<= (TEMP_SENSOR_REG  &	~mask) | (PWDATA & mask);
                    32'h0000_0014: ADC_CTRL_REG		<= (ADC_CTRL_REG     &	~mask) | (PWDATA & mask);
                    32'h0000_0018: DBG_CTRL_REG		<= (DBG_CTRL_REG     &	~mask) | (PWDATA & mask);
                    32'h0000_001c: GPIO_DATA_REG	<= (GPIO_DATA_REG    &	~mask) | (PWDATA & mask);
                    32'h0000_0020: DAC_OUTPUT_REG	<= (DAC_OUTPUT_REG   &	~mask) | (PWDATA & mask);
                    32'h0000_0024: VOLTAGE_CTRL_REG	<= (VOLTAGE_CTRL_REG &	~mask) | (PWDATA & mask);
                    32'h0000_0028: CLK_CONFIG_REG	<= (CLK_CONFIG_REG   &	~mask) | (PWDATA & mask);
                    32'h0000_002c: TIMER_COUNT_REG	<= (TIMER_COUNT_REG  &	~mask) | (PWDATA & mask);
                    32'h0000_0030: INPUT_DATA_REG	<= (INPUT_DATA_REG   &	~mask) | (PWDATA & mask);
                    32'h0000_0034: OUTPUT_DATA_REG	<= (OUTPUT_DATA_REG  &	~mask) | (PWDATA & mask);
                    32'h0000_0038: DMA_CTRL_REG		<= (DMA_CTRL_REG     &	~mask) | (PWDATA & mask);
                    32'h0000_003c: SYS_CTRL_REG		<= (SYS_CTRL_REG     &	~mask) | (PWDATA & mask);
                    default : ;
                endcase
            end
            else begin
                case (reg_addr)
                    32'h0000_0000: PRDATA <= SYS_STATUS_REG;
                    32'h0000_0004: PRDATA <= INT_CTRL_REG;
                    32'h0000_0008: PRDATA <= DEV_ID_REG;
                    32'h0000_000c: PRDATA <= MEM_CTRL_REG;
                    32'h0000_0010: PRDATA <= TEMP_SENSOR_REG;
                    32'h0000_0014: PRDATA <= ADC_CTRL_REG;
                    32'h0000_0018: PRDATA <= DBG_CTRL_REG;
                    32'h0000_001c: PRDATA <= GPIO_DATA_REG;
                    32'h0000_0020: PRDATA <= DAC_OUTPUT_REG;
                    32'h0000_0024: PRDATA <= VOLTAGE_CTRL_REG;
                    32'h0000_0028: PRDATA <= CLK_CONFIG_REG;
                    32'h0000_002c: PRDATA <= TIMER_COUNT_REG;
                    32'h0000_0030: PRDATA <= INPUT_DATA_REG;
                    32'h0000_0034: PRDATA <= OUTPUT_DATA_REG;
                    32'h0000_0038: PRDATA <= DMA_CTRL_REG;
                    32'h0000_003c: PRDATA <= SYS_CTRL_REG;
                    default : ;
                endcase
            end
        end
        else begin
            PREADY <= 0;
            PRDATA <= 0;
        end
    end
end

endmodule