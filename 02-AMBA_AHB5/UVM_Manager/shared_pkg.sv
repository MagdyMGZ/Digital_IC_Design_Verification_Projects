package shared_pkg;
    parameter  DATA_WIDTH   = 32;
    parameter  ADDR_WIDTH   = 32;
    parameter  HBURST_WIDTH = 3;
    parameter  MEM_DEPTH    = 64;
    localparam STRB_WIDTH   = DATA_WIDTH/8;
    localparam OFFSET       = $clog2(MEM_DEPTH);

    typedef enum bit {READ = 0 , WRITE = 1} type_e;
    typedef enum bit [2:0] {SINGLE = 3'b000, INCR   = 3'b001, WRAP4  = 3'b010, INCR4  = 3'b011, WRAP8  = 3'b100, INCR8  = 3'b101, WRAP16 = 3'b110, INCR16 = 3'b111} hburst_e;
    typedef enum bit [2:0] {BYTE = 3'b000, HALFWORD = 3'b001, WORD = 3'b010} hsize_e;
    typedef enum bit [1:0] {IDLE = 2'b00, BUSY = 2'b01, NONSEQ = 2'b10, SEQ = 2'b11} htrans_e;
endpackage