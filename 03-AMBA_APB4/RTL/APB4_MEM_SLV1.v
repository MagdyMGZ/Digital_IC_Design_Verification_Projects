////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : APB4_MEM_SLV1.v 
////////////////////////////////////////////////////////////////////////////////
module APB4_MEM_SLV1 #(
    parameter  DATA_WIDTH = 32,
    parameter  ADDR_WIDTH = 32,
    parameter  MEM_DEPTH  = 64,
    localparam STRB_WIDTH = DATA_WIDTH/8,
    localparam WORD_ADDR  = $clog2(MEM_DEPTH)
) (
    input       wire                                PCLK,
    input       wire                                PRESETn,
    input       wire        [ADDR_WIDTH-1:0]        PADDR,
    input       wire                                PSEL1,
    input       wire                                PENABLE,
    input       wire                                PWRITE,
    input       wire        [DATA_WIDTH-1:0]        PWDATA,
    input       wire        [STRB_WIDTH-1:0]        PSTRB,
    output      reg                                 PREADY,
    output      reg         [DATA_WIDTH-1:0]        PRDATA,
    output      reg                                 PSLVERR
);

reg [DATA_WIDTH-1:0] MEM [MEM_DEPTH-1:0];

reg [WORD_ADDR-1:0] word_addr;
wire [DATA_WIDTH-1:0] mask;

genvar i;
generate
    for (i = 0 ; i < STRB_WIDTH ; i = i + 1) begin
        assign mask[i*8 +: 8] = {8{PSTRB[i]}};
    end
endgenerate

always @(*) begin
    if (PSEL1 && PENABLE) begin
        word_addr = PADDR[WORD_ADDR-1:0];
        if (word_addr > (MEM_DEPTH-1))
            PSLVERR = 1;
        else
            PSLVERR = 0;
    end
    else begin
        word_addr = 0;
        PSLVERR = 0;
    end
end

always @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
        PREADY <= 0;
        PRDATA <= 0;
    end
    else begin
        if (PSEL1 && PENABLE && ~PSLVERR) begin
            PREADY <= 1;
            if (PWRITE)
                MEM[word_addr] <= (MEM[word_addr] & ~mask) | (PWDATA & mask);
            else
                PRDATA <= MEM[word_addr];
        end
        else begin
            PREADY <= 0;
            PRDATA <= 0;
        end
    end
end

endmodule