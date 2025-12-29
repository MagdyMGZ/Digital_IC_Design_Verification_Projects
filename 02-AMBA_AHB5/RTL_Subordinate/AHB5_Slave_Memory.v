////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : AHB5_Slave_Memory.v 
////////////////////////////////////////////////////////////////////////////////
module AHB5_Slave_Memory #(
    parameter  DATA_WIDTH   = 32,
    parameter  ADDR_WIDTH   = 32,
    parameter  HBURST_WIDTH = 3,
    parameter  MEM_DEPTH    = 64,
    localparam STRB_WIDTH   = DATA_WIDTH/8,
    localparam OFFSET       = $clog2(MEM_DEPTH)
) (
    input       wire                                HCLK,
    input       wire                                HRESETn,
    input       wire                                HSEL1,
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

localparam  SINGLE = 3'b000,
            INCR   = 3'b001,
            WRAP4  = 3'b010,
            INCR4  = 3'b011,
            WRAP8  = 3'b100,
            INCR8  = 3'b101,
            WRAP16 = 3'b110,
            INCR16 = 4'b111;

reg [7:0] MEM [0:MEM_DEPTH-1];  // Little Endian Order - Byte Accessible

// Offset signal from base address
wire [OFFSET-1:0] address;

// STRB Signal
wire [DATA_WIDTH-1:0] mask;

// HRESP Signals
reg error_first_cycle;
reg error_second_cycle;

// HREADY Signal
reg HREADY_SLV;

// Offset Decoding logic
assign address  = HADDR[OFFSET-1:0];

// STRB logic
genvar i;
generate
    for (i = 0 ; i < STRB_WIDTH ; i = i + 1) begin
        assign mask[i*8 +: 8] = {8{HWSTRB[i]}};
    end
endgenerate

// Error Cycles logic
always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
        error_first_cycle <= OKAY;
        error_second_cycle <= OKAY;    
    end 
    else begin
        if (HREADY && HSEL1) begin
            if (error_first_cycle) begin
                error_first_cycle <= OKAY;
                error_second_cycle <= ERROR;
            end else if ((address > (MEM_DEPTH-1)) || ((8 << HSIZE) > DATA_WIDTH)) begin
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
        if (HREADY && HSEL1 && !HRESP) begin
            if ((HTRANS == NONSEQ) || (HTRANS == SEQ)) begin
                HREADY_SLV <= 1;
                if (HWRITE) begin // Write Operation
                    case (HSIZE)
                        BYTE : begin
                            MEM[address+0] <= ((HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                        end
                        HALFWORD : begin
                            MEM[address+0] <= ((HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                        end
                        WORD : begin
                            MEM[address+0] <= ((HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] <= ((HWDATA[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] <= ((HWDATA[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end 
                        default : begin
                            MEM[address+0] <= ((HWDATA[7:0] & mask[7:0]) | (MEM[address+0] & ~mask[7:0]));
                            MEM[address+1] <= ((HWDATA[15:8] & mask[15:8]) | (MEM[address+1] & ~mask[15:8]));
                            MEM[address+2] <= ((HWDATA[23:16] & mask[23:16]) | (MEM[address+2] & ~mask[23:16]));
                            MEM[address+3] <= ((HWDATA[31:24] & mask[31:24]) | (MEM[address+3] & ~mask[31:24]));
                        end
                    endcase
                    HRDATA <= 0;
                end
                else begin // Read Operation
                    case (HSIZE)
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