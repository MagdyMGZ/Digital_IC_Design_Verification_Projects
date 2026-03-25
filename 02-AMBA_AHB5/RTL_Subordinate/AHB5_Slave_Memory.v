////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : AHB5_Slave_Memory.v 
////////////////////////////////////////////////////////////////////////////////
module AHB5_Slave_Memory #(
    parameter  DATA_WIDTH   = 32,
    parameter  ADDR_WIDTH   = 32,
    parameter  HBURST_WIDTH = 3,
    parameter  MEM_DEPTH    = 256,
    localparam STRB_WIDTH   = DATA_WIDTH/8,
    localparam OFFSET       = $clog2(MEM_DEPTH)
) (
    input       wire                                HCLK,
    input       wire                                HRESETn,
    input       wire                                HSELx,
    input       wire                                HREADY,
    input       wire        [ADDR_WIDTH-1:0]        HADDR,
    input       wire        [HBURST_WIDTH-1:0]      HBURST,
    input       wire        [2:0]                   HSIZE,
    input       wire        [1:0]                   HTRANS,
    input       wire        [DATA_WIDTH-1:0]        HWDATA,
    input       wire        [STRB_WIDTH-1:0]        HWSTRB,
    input       wire                                HWRITE,
    output      reg         [DATA_WIDTH-1:0]        HRDATA,
    output      reg                                 HREADYOUT,
    output      reg                                 HRESP
);

// Signals to Register Inputs
reg                    HSELx_FF;
reg                    HREADY_FF;
reg [ADDR_WIDTH-1:0]   HADDR_FF;
reg [HBURST_WIDTH-1:0] HBURST_FF;
reg [2:0]              HSIZE_FF;
reg [1:0]              HTRANS_FF;
reg [DATA_WIDTH-1:0]   HWDATA_FF;
reg                    HWRITE_FF;
reg [STRB_WIDTH-1:0]   HWSTRB_FF;

// Data Memory
reg [DATA_WIDTH-1:0] data_memory [0:MEM_DEPTH-1];

// Offset signal from base address
wire [OFFSET-1:0] offset;

// STRB Signal
wire [DATA_WIDTH-1:0] mask;
wire [DATA_WIDTH-1:0] HWDATA_mask;

// HRESP Signal
wire invalid_trans;

// HADDR (Base Address) Decoder logic
assign offset = HADDR_FF[OFFSET-1:0];

// Invalid Transfers logic
assign invalid_trans = ((offset > (MEM_DEPTH-1)) || ((8 << HSIZE_FF) > DATA_WIDTH));

// STRB logic
genvar i;
generate
    for (i = 0 ; i < STRB_WIDTH ; i = i + 1) begin
        assign mask[i*8 +: 8] = {8{HWSTRB_FF[i]}};
    end
endgenerate

assign HWDATA_mask = ((HWDATA_FF & mask) | (data_memory[offset] & ~mask));

// Address Phase for Pipelining
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
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
        HSELx_FF  <= HSELx;
        HREADY_FF <= HREADY;
        HADDR_FF  <= HADDR;
        HBURST_FF <= HBURST;
        HSIZE_FF  <= HSIZE;
        HTRANS_FF <= HTRANS;
        HWDATA_FF <= HWDATA;
        HWRITE_FF <= HWRITE;
        HWSTRB_FF <= HWSTRB;
    end
end

// Data Transfer Phase
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
        HRESP <= 0;
        HREADYOUT <= 0;
        HRDATA <= 0;
    end
    else begin
        if (HREADY_FF && HSELx_FF) begin
            if (invalid_trans) begin
                HRESP <= 1;         // ERROR TRANS
                HREADYOUT <= 1;     // OUT READY
            end
            else begin
                HRESP <= 0;         // OKAY TRANS
                if ((HTRANS_FF == 2'b10) || (HTRANS_FF == 2'b11)) begin // TRANS = NONSEQ or SEQ
                    HREADYOUT <= 1;                                     // OUT READY
                    if (HWRITE_FF) begin                                // WRITE OPPERATION
                        case ({offset[1:0],HSIZE_FF})
                            5'b00_000 : data_memory[offset] <= HWDATA_mask[7:0];    // 1st  BYTE
                            5'b00_001 : data_memory[offset] <= HWDATA_mask[15:0];   // 1st  HALFWORD
                            5'b00_010 : data_memory[offset] <= HWDATA_mask;         // FULL WORD
                            5'b01_000 : data_memory[offset] <= HWDATA_mask[15:8];   // 2nd  BYTE
                            5'b10_000 : data_memory[offset] <= HWDATA_mask[23:16];  // 3rd  BYTE
                            5'b10_001 : data_memory[offset] <= HWDATA_mask[31:16];  // 2nd  HALFWORD
                            5'b11_000 : data_memory[offset] <= HWDATA_mask[31:24];  // 4th  BYTE
                            default   : data_memory[offset] <= HWDATA_mask;         // FULL WORD
                        endcase
                    end
                    else begin      // READ OPERATION
                        case ({offset[1:0],HSIZE_FF})
                            5'b00_000 : HRDATA <= data_memory[offset][7:0];    // 1st  BYTE
                            5'b00_001 : HRDATA <= data_memory[offset][15:0];   // 1st  HALFWORD
                            5'b00_010 : HRDATA <= data_memory[offset];         // FULL WORD
                            5'b01_000 : HRDATA <= data_memory[offset][15:8];   // 2nd  BYTE
                            5'b10_000 : HRDATA <= data_memory[offset][23:16];  // 3rd  BYTE
                            5'b10_001 : HRDATA <= data_memory[offset][31:16];  // 2nd  HALFWORD
                            5'b11_000 : HRDATA <= data_memory[offset][31:24];  // 4th  BYTE
                            default   : HRDATA <= data_memory[offset];         // FULL WORD
                        endcase
                    end
                end
                else begin          // TRANS = BUSY or IDLE
                    HREADYOUT <= 0; // OUT NOT READY
                end
            end
        end
        else begin                  // HSEL NOT READY
            HRESP <= 0;             // ERROR
            HREADYOUT <= 0;         // OUT NOT READY
        end 
    end
end

endmodule


// Another Version
/*
module AHB5_Slave_Memory #(
    parameter  DATA_WIDTH   = 32,
    parameter  ADDR_WIDTH   = 32,
    parameter  HBURST_WIDTH = 3,
    parameter  MEM_DEPTH    = 256 *4,
    localparam STRB_WIDTH   = DATA_WIDTH/8,
    localparam OFFSET       = $clog2(MEM_DEPTH)
) (
    input       wire                                HCLK,
    input       wire                                HRESETn,
    input       wire                                HSELx,
    input       wire                                HREADY,
    input       wire        [ADDR_WIDTH-1:0]        HADDR,
    input       wire        [HBURST_WIDTH-1:0]      HBURST,
    input       wire        [2:0]                   HSIZE,
    input       wire        [1:0]                   HTRANS,
    input       wire        [DATA_WIDTH-1:0]        HWDATA,
    input       wire        [STRB_WIDTH-1:0]        HWSTRB,
    input       wire                                HWRITE,
    output      reg         [DATA_WIDTH-1:0]        HRDATA,
    output      reg                                 HREADYOUT,
    output      reg                                 HRESP
);

localparam  OKAY  = 0,
            ERROR = 1;

localparam  IDLE   = 2'b00,
            BUSY   = 2'b01,
            NONSEQ = 2'b10,
            SEQ    = 2'b11;

localparam  BYTE     = 3'b000, // 8  bits
            HALFWORD = 3'b001, // 16 bits
            WORD     = 3'b010; // 32 bits

// Signals to Register Inputs
reg                    HSELx_FF;
reg                    HREADY_FF;
reg [ADDR_WIDTH-1:0]   HADDR_FF;
reg [HBURST_WIDTH-1:0] HBURST_FF;
reg [2:0]              HSIZE_FF;
reg [1:0]              HTRANS_FF;
reg [DATA_WIDTH-1:0]   HWDATA_FF;
reg                    HWRITE_FF;
reg [STRB_WIDTH-1:0]   HWSTRB_FF;

// Data Memory
reg [7:0] MEM [0:MEM_DEPTH-1];  // Little Endian Order - Byte Accessible

// Offset signal from base address
wire [OFFSET-1:0] address;

// STRB Signal
wire [DATA_WIDTH-1:0] mask;

// HRESP Signal
wire invalid_trans;

// HRESP Signals
reg error_first_cycle;
reg error_second_cycle;

// HREADY Signal
reg HREADY_SLV;

// Offset Decoding logic
assign address  = HADDR_FF[OFFSET-1:0];

// Invalid Transfers logic
assign invalid_trans = ((address > (MEM_DEPTH-1)) || ((8 << HSIZE_FF) > DATA_WIDTH));

// STRB logic
genvar i;
generate
    for (i = 0 ; i < STRB_WIDTH ; i = i + 1) begin
        assign mask[i*8 +: 8] = {8{HWSTRB_FF[i]}};
    end
endgenerate

// Address Phase for Pipelining
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
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
        HSELx_FF  <= HSELx;
        HREADY_FF <= HREADY;
        HADDR_FF  <= HADDR;
        HBURST_FF <= HBURST;
        HSIZE_FF  <= HSIZE;
        HTRANS_FF <= HTRANS;
        HWDATA_FF <= HWDATA;
        HWRITE_FF <= HWRITE;
        HWSTRB_FF <= HWSTRB;
    end
end

// Error Cycles logic
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
        error_first_cycle <= OKAY;
        error_second_cycle <= OKAY;    
    end 
    else begin
        if (HREADY_FF && HSELx_FF) begin
            if (error_first_cycle) begin
                error_first_cycle <= OKAY;
                error_second_cycle <= ERROR;
            end else if (invalid_trans) begin
                error_first_cycle <= ERROR;
                error_second_cycle <= OKAY;
            end else begin
                error_first_cycle <= OKAY;
                error_second_cycle <= OKAY;
            end
        end
        else begin
            error_first_cycle <= OKAY;
            error_second_cycle <= OKAY; 
        end
    end
end

// Write and Read logic
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
        HREADY_SLV <= 0;
        HRDATA <= 0;
    end
    else begin
        if (HREADY_FF && HSELx_FF && !invalid_trans) begin
            if ((HTRANS_FF == NONSEQ) || (HTRANS_FF == SEQ)) begin
                HREADY_SLV <= 1;
                if (HWRITE_FF) begin // Write Operation
                    case (HSIZE_FF)
                        BYTE : begin
                            MEM[address+0] <= ((HWDATA_FF[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                        end
                        HALFWORD : begin
                            MEM[address+0] <= ((HWDATA_FF[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA_FF[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                        end
                        WORD : begin
                            MEM[address+0] <= ((HWDATA_FF[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA_FF[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] <= ((HWDATA_FF[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] <= ((HWDATA_FF[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end 
                        default : begin
                            MEM[address+0] <= ((HWDATA_FF[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA_FF[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] <= ((HWDATA_FF[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] <= ((HWDATA_FF[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end
                    endcase
                    HRDATA <= 0;
                end
                else begin // Read Operation
                    case (HSIZE_FF)
                        BYTE     : HRDATA <= {24'b0,MEM[address+0]};
                        HALFWORD : HRDATA <= {16'b0,MEM[address+1],MEM[address+0]};
                        WORD     : HRDATA <= {MEM[address+3],MEM[address+2],MEM[address+1],MEM[address+0]};
                        default  : HRDATA <= {MEM[address+3],MEM[address+2],MEM[address+1],MEM[address+0]};
                    endcase
                end
            end
            else begin
                HREADY_SLV <= 0;
                HRDATA <= 0;
            end
        end
        else begin
            HREADY_SLV <= 0;
            HRDATA <= 0;
        end
    end
end

// HRESP and HREADYOUT logic
always @(*) begin
    if (!HRESETn) begin
        HRESP = OKAY; 
        HREADYOUT = 0;
    end
    else begin
        if (error_second_cycle) begin
            HRESP = ERROR;
            HREADYOUT = 1;
        end
        else if (error_first_cycle) begin
            HRESP = ERROR;
            HREADYOUT = 0;
        end
        else begin
            HRESP = OKAY;
            if (HREADY_SLV) begin
                HREADYOUT = 1;
            end
            else begin
                HREADYOUT = 0;
            end
        end
    end
end

endmodule
*/
