module Control_Unit (
    input       wire        [6:0]       op,
    input       wire                    Zero,
    input       wire                    sign_flag,
    input       wire        [2:0]       funct3,
    input       wire                    funct7,
    output      reg                     PCSrc,
    output      reg                     ResultSrc,
    output      reg                     MemWrite,
    output      reg                     ALUSrc,
    output      reg         [1:0]       ImmSrc,
    output      reg                     RegWrite,
    output      reg         [2:0]       ALUControl
);

reg      [1:0]       ALUOp;
reg                  Branch;
wire                 beq, bnq, blt;

always @(*) begin
    case (ALUOp)
        2'b00 : begin                          // ADD (lw,sw)
            ALUControl = 3'b000;
        end

        2'b01 : begin
            case (funct3)
                3'b000  : ALUControl = 3'b010; // BEQ
                3'b001  : ALUControl = 3'b010; // BNQ
                3'b100  : ALUControl = 3'b010; // BLT
                default : ALUControl = 3'b000;
            endcase
        end
        
        2'b10 : begin
            case (funct3)
                3'b000  : begin
                    if ({op[5],funct7} == 2'b11)
                        ALUControl = 3'b010;     // SUB
                    else
                        ALUControl = 3'b000;     // ADD
                end
                3'b001  : ALUControl = 3'b001;   // SHL
                3'b100  : ALUControl = 3'b100;   // XOR
                3'b101  : ALUControl = 3'b101;   // SHR
                3'b110  : ALUControl = 3'b110;   // OR
                3'b111  : ALUControl = 3'b111;   // AND
                default : ALUControl = 3'b000;
            endcase
        end

        default : ALUControl = 3'b000;
    endcase
end

always @(*) begin
    casex (op)
        7'b000_0011 : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b1001_01000; // Load Word
        7'b010_0011 : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b0011_1x000; // Store Word
        7'b011_0011 : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b1xx0_00010; // R-Type
        7'b001_0011 : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b1001_00010; // I-Type
        7'b110_0011 : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b0100_0x101; // Branch Instructions
        default     : {RegWrite,ImmSrc,ALUSrc,MemWrite,ResultSrc,Branch,ALUOp} = 9'b0000_00000;
    endcase
end

always @(*) begin
    case (funct3)
        3'b000  : PCSrc = beq;        // BEQ
        3'b001  : PCSrc = bnq;        // BNQ
        3'b100  : PCSrc = blt;        // BLT
        default : PCSrc = 1'b0;
    endcase
end

assign beq = Branch & Zero;
assign bnq = Branch & (~Zero);
assign blt = Branch & sign_flag;

endmodule