////////////////////////////////////////////////////////////////////////////////
// Author : Magdy Ahmed Abbas
// File   : APB4_DECODER.v 
////////////////////////////////////////////////////////////////////////////////
module APB4_DECODER #(
    parameter DATA_WIDTH = 32
) (
    input       wire                                PSELx,
    input       wire        [DATA_WIDTH-1:0]        PRDATA0,
    input       wire        [DATA_WIDTH-1:0]        PRDATA1,
    input       wire                                PREADY0,
    input       wire                                PREADY1,
    input       wire                                PSLVERR0,
    input       wire                                PSLVERR1,
    output      reg                                 PSEL0,
    output      reg                                 PSEL1,
    output      reg         [DATA_WIDTH-1:0]        PRDATA,
    output      reg                                 PREADY,
    output      reg                                 PSLVERR
);

always @(*) begin
    case (PSELx)
        1'b0 : begin
            PSEL0   = 1;
            PSEL1   = 0;
            PRDATA  = PRDATA0;
            PREADY  = PREADY0;
            PSLVERR = PSLVERR0;
        end
        1'b1 : begin
            PSEL0   = 0;
            PSEL1   = 1;
            PRDATA  = PRDATA1;
            PREADY  = PREADY1;
            PSLVERR = PSLVERR1;
        end
        default : begin
            PSEL0   = 0;
            PSEL1   = 0;
            PRDATA  = 0;
            PREADY  = 0;
            PSLVERR = 0;
        end
    endcase
end
    
endmodule