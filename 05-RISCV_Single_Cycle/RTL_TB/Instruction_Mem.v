module Instruction_Mem (
    input       wire        [31:0]      PC,
    output      wire        [31:0]      Instr
);

reg     [31:0]      RAM       [63:0];

assign Instr = RAM[PC[31:2]];

endmodule