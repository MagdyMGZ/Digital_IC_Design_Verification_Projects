module RISCV (
    input       logic        clk,
    input       logic        areset
);

logic      [31:0]      PCNext;
logic      [31:0]      PC;
logic      [31:0]      PCPlus4;
logic      [31:0]      Instr;
logic      [31:0]      ImmExt;
logic      [31:0]      PCTarget;
logic      [31:0]      Result;
logic      [31:0]      RD2;
logic      [31:0]      SrcA;
logic      [31:0]      SrcB;
logic      [31:0]      ALUResult;
logic      [31:0]      ReadData;

logic                  PCSrc, ResultSrc, MemWrite, ALUSrc, RegWrite;
logic                  Zero, sign_flag;

logic      [1:0]       ImmSrc;
logic      [2:0]       ALUControl;

// PC + 4 Adder
Adder pc_plus4 (
    .In1(PC),
    .In2(4),
    .Out(PCPlus4)
);

// PC Target Adder
Adder pc_traget (
    .In1(PC),
    .In2(ImmExt),
    .Out(PCTarget)
);

// PC MUX
MUX pc_mux (
    .In1(PCPlus4),
    .In2(PCTarget),
    .Sel(PCSrc),
    .Out(PCNext)
);

// Program Counter (PC)
PC pc (
    .areset(areset),
    .clk(clk),
    .PCNext(PCNext),
    .PC(PC)
);

// Instruction Memory
Instruction_Mem instr_mem (
    .PC(PC),
    .Instr(Instr)
);

// Register File
Register_File reg_file (
    .areset(areset),
    .clk(clk),
    .WE3(RegWrite),
    .A1(Instr[19:15]),
    .A2(Instr[24:20]),
    .A3(Instr[11:7]),
    .WD3(Result),
    .RD1(SrcA),
    .RD2(RD2)
);

// Sign Extender
Sign_Extend sign_extender (
    .ImmSrc(ImmSrc),
    .Instr(Instr[31:7]),
    .ImmExt(ImmExt)
);

// ALU MUX
MUX alu_mux (
    .In1(RD2),
    .In2(ImmExt),
    .Sel(ALUSrc),
    .Out(SrcB)
);

// ALU
ALU alu (
    .ALUControl(ALUControl),
    .SrcA(SrcA),
    .SrcB(SrcB),
    .Zero(Zero),
    .sign_flag(sign_flag),
    .ALUResult(ALUResult)
);

// Control Unit
Control_Unit control_unit (
    .op(Instr[6:0]),
    .Zero(Zero),
    .sign_flag(sign_flag),
    .funct3(Instr[14:12]),
    .funct7(Instr[30]),
    .PCSrc(PCSrc),
    .ResultSrc(ResultSrc),
    .MemWrite(MemWrite),
    .ALUSrc(ALUSrc),
    .ImmSrc(ImmSrc),
    .RegWrite(RegWrite),
    .ALUControl(ALUControl)
);

// Data Memory
Data_Memory data_mem (
    .clk(clk),
    .areset(areset),
    .WE(MemWrite),
    .A(ALUResult),
    .WD(RD2),
    .RD(ReadData)
);

// Result MUX
MUX result_mux (
    .In1(ALUResult),
    .In2(ReadData),
    .Sel(ResultSrc),
    .Out(Result)
);

`ifdef SIM

always_comb begin
    if (!areset) begin
        RST_assertion : assert final (PC == 0);
        RST_cover     : cover  final (PC == 0);
    end
end

always_comb begin
    case (ImmSrc)
        2'b00   : begin
            ImmExt_assertion_00 : assert final (ImmExt == {{20{Instr[31]}},Instr[31:20]}); 
            ImmExt_cover_00     : cover  final (ImmExt == {{20{Instr[31]}},Instr[31:20]}); 
        end
        2'b01   : begin
            ImmExt_assertion_01 : assert final (ImmExt == {{20{Instr[31]}},Instr[31:25],Instr[11:7]}); 
            ImmExt_cover_01     : cover  final (ImmExt == {{20{Instr[31]}},Instr[31:25],Instr[11:7]}); 
        end 
        2'b10   : begin
            ImmExt_assertion_10 : assert final (ImmExt == {{20{Instr[31]}},Instr[7],Instr[30:25],Instr[11:8],1'b0}); 
            ImmExt_cover_10     : cover  final (ImmExt == {{20{Instr[31]}},Instr[7],Instr[30:25],Instr[11:8],1'b0}); 
        end
        default : begin
            ImmExt_assertion_11 : assert final (ImmExt == 0); 
            ImmExt_cover_11     : cover  final (ImmExt == 0); 
        end
    endcase
end

always_comb begin
    if (ALUSrc) begin
        SrcB_assertion_1 : assert final (SrcB == ImmExt);
        SrcB_cover_1     : cover  final (SrcB == ImmExt);
    end
    else if (!ALUSrc) begin
        SrcB_assertion_0 : assert final (SrcB == RD2);
        SrcB_cover_0     : cover  final (SrcB == RD2);
    end
end

always_comb begin
    if (PCSrc) begin
        PCNext_assertion_1 : assert final (PCNext == PCTarget);
        PCNext_cover_1     : cover  final (PCNext == PCTarget);
    end
    else if (!PCSrc) begin
        PCNext_assertion_0 : assert final (PCNext == PCPlus4);
        PCNext_cover_0     : cover  final (PCNext == PCPlus4);
    end
end

always_comb begin
    case (ALUControl)
        3'b000  : begin
            ALU_assertion_0 : assert final (ALUResult == SrcA  +  SrcB);
            ALU_cover_0     : assert final (ALUResult == SrcA  +  SrcB);
        end
        
        3'b001  : begin
            ALU_assertion_1 : assert final (ALUResult == SrcA  << SrcB);
            ALU_cover_1     : assert final (ALUResult == SrcA  << SrcB);
        end

        3'b010  : begin
            ALU_assertion_2 : assert final (ALUResult == SrcA  -  SrcB);
            ALU_cover_2     : assert final (ALUResult == SrcA  -  SrcB);
        end

        3'b100  : begin
            ALU_assertion_4 : assert final (ALUResult == SrcA  ^  SrcB);
            ALU_cover_4     : assert final (ALUResult == SrcA  ^  SrcB);
        end

        3'b101  : begin
            ALU_assertion_5 : assert final (ALUResult == SrcA  >> SrcB);
            ALU_cover_5     : assert final (ALUResult == SrcA  >> SrcB);
        end

        3'b110  : begin
            ALU_assertion_6 : assert final (ALUResult == SrcA  |  SrcB);
            ALU_cover_6     : assert final (ALUResult == SrcA  |  SrcB);
        end

        3'b111  : begin
            ALU_assertion_7 : assert final (ALUResult == SrcA  &  SrcB);
            ALU_cover_7     : assert final (ALUResult == SrcA  &  SrcB);
        end

        default : begin
            ALU_assertion_3 : assert final (ALUResult == 0);
            ALU_cover_3     : assert final (ALUResult == 0);
        end
    endcase
end

always_comb begin
    if (ResultSrc) begin
        Result_assertion_1 : assert final (Result == ReadData);
        Result_cover_1     : cover  final (Result == ReadData);
    end
    else if (!ResultSrc) begin
        Result_assertion_0 : assert final (Result == ALUResult);
        Result_cover_0     : cover  final (Result == ALUResult);
    end
end

property pc_property;
    @(posedge clk) disable iff(!areset) areset |=> (PC == $past(PCNext)); 
endproperty

PC_assertion : assert property (pc_property);
PC_cover     : cover  property (pc_property);

`endif

endmodule
