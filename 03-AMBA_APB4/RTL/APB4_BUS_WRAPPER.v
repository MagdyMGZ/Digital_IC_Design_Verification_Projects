////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : APB4_BUS_WRAPPER.v 
////////////////////////////////////////////////////////////////////////////////
module APB4_BUS_WRAPPER #(
    parameter  DATA_WIDTH = 32,
    parameter  ADDR_WIDTH = 32,
    parameter  MEM_DEPTH  = 64,
    localparam STRB_WIDTH = DATA_WIDTH/8
) (
    input       wire                                PCLK,
    input       wire                                PRESETn,
    input       wire                                TRANSFER,
    input       wire                                WRITE,
    input       wire        [ADDR_WIDTH-1:0]        ADDR,
    input       wire        [DATA_WIDTH-1:0]        WDATA,
    input       wire        [STRB_WIDTH-1:0]        STRB,
    output      wire                                READY,
    output      wire        [DATA_WIDTH-1:0]        RDATA,
    output      wire                                SLVERR
);

wire                  PSELx, PENABLE;
wire [DATA_WIDTH-1:0] PRDATA0, PRDATA1;
wire                  PSEL0, PSEL1, PREADY0, PREADY1, PSLVERR0, PSLVERR1;
wire [DATA_WIDTH-1:0] PRDATA_DECODER;
wire                  PREADY_DECODER, PSLVERR_DECODER;
wire [ADDR_WIDTH-1:0] PADDR;
wire                  PWRITE;
wire [DATA_WIDTH-1:0] PWDATA;
wire [STRB_WIDTH-1:0] PSTRB;

APB4_MASTER_BRIDGE #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH)) apb4_master_bridge (
    .PCLK(PCLK),
    .PRESETn(PRESETn),
    .TRANSFER(TRANSFER),
    .PADDR_BUS(ADDR),
    .PWRITE_BUS(WRITE),
    .PWDATA_BUS(WDATA),
    .PSTRB_BUS(STRB),
    .PREADY_DECODER(PREADY_DECODER),
    .PRDATA_DECODER(PRDATA_DECODER),
    .PSLVERR_DECODER(PSLVERR_DECODER),
    .PADDR(PADDR),
    .PWRITE(PWRITE),
    .PWDATA(PWDATA),
    .PSTRB(PSTRB),
    .PSELx(PSELx),
    .PENABLE(PENABLE),
    .PREADY(READY),
    .PRDATA(RDATA),
    .PSLVERR(SLVERR)
);

APB4_DECODER #(.DATA_WIDTH(DATA_WIDTH)) apb4_decoder (
    .PSELx(PSELx),
    .PRDATA0(PRDATA0),
    .PRDATA1(PRDATA1),
    .PREADY0(PREADY0),
    .PREADY1(PREADY1),
    .PSLVERR0(PSLVERR0),
    .PSLVERR1(PSLVERR1),
    .PSEL0(PSEL0),
    .PSEL1(PSEL1),
    .PRDATA(PRDATA_DECODER),
    .PREADY(PREADY_DECODER),
    .PSLVERR(PSLVERR_DECODER)
);

APB4_REGFILE_SLV0 #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH)) apb4_regfile_slv0 (
    .PCLK(PCLK),
    .PRESETn(PRESETn),
    .PADDR(PADDR),
    .PSEL0(PSEL0),
    .PENABLE(PENABLE),
    .PWRITE(PWRITE),
    .PWDATA(PWDATA),
    .PSTRB(PSTRB),
    .PREADY(PREADY0),
    .PRDATA(PRDATA0),
    .PSLVERR(PSLVERR0)
);

APB4_MEM_SLV1 #(.DATA_WIDTH(DATA_WIDTH),.ADDR_WIDTH(ADDR_WIDTH),.MEM_DEPTH(MEM_DEPTH)) apb4_mem_slv1 (
    .PCLK(PCLK),
    .PRESETn(PRESETn),
    .PADDR(PADDR),
    .PSEL1(PSEL1),
    .PENABLE(PENABLE),
    .PWRITE(PWRITE),
    .PWDATA(PWDATA),
    .PSTRB(PSTRB),
    .PREADY(PREADY1),
    .PRDATA(PRDATA1),
    .PSLVERR(PSLVERR1)
);

endmodule