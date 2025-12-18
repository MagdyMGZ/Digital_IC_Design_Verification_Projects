////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : APB4_MASTER_BRIDGE.v 
////////////////////////////////////////////////////////////////////////////////
module APB4_MASTER_BRIDGE #(
    parameter  DATA_WIDTH = 32,
    parameter  ADDR_WIDTH = 32,
    localparam STRB_WIDTH = DATA_WIDTH/8
) (
    input       wire                                PCLK,
    input       wire                                PRESETn,
    input       wire                                TRANSFER,
    input       wire        [ADDR_WIDTH-1:0]        PADDR_BUS,
    input       wire                                PWRITE_BUS,
    input       wire        [DATA_WIDTH-1:0]        PWDATA_BUS,
    input       wire        [STRB_WIDTH-1:0]        PSTRB_BUS,
    input       wire                                PREADY_DECODER,
    input       wire        [DATA_WIDTH-1:0]        PRDATA_DECODER,
    input       wire                                PSLVERR_DECODER,
    output      reg         [ADDR_WIDTH-1:0]        PADDR,
    output      reg                                 PWRITE,
    output      reg         [DATA_WIDTH-1:0]        PWDATA,
    output      reg         [STRB_WIDTH-1:0]        PSTRB,
    output      reg                                 PSELx,
    output      reg                                 PENABLE,
    output      wire                                PREADY,
    output      wire        [DATA_WIDTH-1:0]        PRDATA,
    output      wire                                PSLVERR
);

localparam  IDLE   = 2'b00,
            SETUP  = 2'b01,
            ACCESS = 2'b10;

reg [1:0] cs, ns;

assign PREADY  = PREADY_DECODER;
assign PRDATA  = PRDATA_DECODER;
assign PSLVERR = PSLVERR_DECODER;

always @(posedge PCLK) begin
    if (!PRESETn)
        cs <= IDLE;
    else
        cs <= ns;
end

always @(*) begin
    case (cs)
        IDLE : begin
            if (TRANSFER)
                ns = SETUP;
            else
                ns = IDLE;
        end

        SETUP : ns = ACCESS;

        ACCESS : begin
            if (!PREADY_DECODER)
                ns = ACCESS;
            else if (TRANSFER)
                ns = SETUP;
            else
                ns = IDLE;
        end
        default : ns = IDLE;
    endcase
end

always @(*) begin
    case (cs)
        IDLE : begin
            PADDR   = 0;
            PWRITE  = 0;
            PWDATA  = 0;
            PSTRB   = 0;
            PSELx   = 0;
            PENABLE = 0;
        end
        SETUP : begin
            PADDR   = PADDR_BUS;
            PWRITE  = PWRITE_BUS;
            PWDATA  = PWDATA_BUS;
            PSTRB   = (PWRITE_BUS)? PSTRB_BUS : 0;
            PSELx   = PADDR_BUS[ADDR_WIDTH-1];
            PENABLE = 0;
        end
        ACCESS : begin
            PADDR   = PADDR_BUS;
            PWRITE  = PWRITE_BUS;
            PWDATA  = PWDATA_BUS;
            PSTRB   = (PWRITE_BUS)? PSTRB_BUS : 0;
            PSELx   = PADDR_BUS[ADDR_WIDTH-1];
            PENABLE = 1;
        end
        default : begin
            PADDR   = 0;
            PWRITE  = 0;
            PWDATA  = 0;
            PSTRB   = 0;
            PSELx   = 0;
            PENABLE = 0;
        end
    endcase
end
    
endmodule