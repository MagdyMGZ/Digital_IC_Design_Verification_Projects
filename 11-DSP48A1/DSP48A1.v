module DSP48A1 (A,B,D,C,CLK,CARRYIN,OPMODE,BCIN,RSTA,RSTB,RSTM,RSTP,RSTC,RSTD,RSTCARRYIN,RSTOPMODE,CEA,CEB,CEM,CEP,CEC,CED,CECARRYIN,CEOPMODE,PCIN,BCOUT,M,CARRYOUT,CARRYOUTF,PCOUT,P);

parameter   A0REG       = 0;
parameter   A1REG       = 1;
parameter   B0REG       = 0;
parameter   B1REG       = 1;
parameter   CREG        = 1;
parameter   DREG        = 1;
parameter   MREG        = 1;
parameter   PREG        = 1;
parameter   CARRYINREG  = 1;
parameter   CARRYOUTREG = 1;
parameter   OPMODEREG   = 1;
parameter   CARRYINSEL  = "OPMODE5"; 
parameter   B_INPUT     = "DIRECT";
parameter   RSTTYPE     = "SYNC";

input [17:0] A, B, D, BCIN;
input [47:0] C, PCIN;
input [7:0]  OPMODE;
input        CLK, CARRYIN, RSTA, RSTB, RSTM, RSTP, RSTC, RSTD, RSTCARRYIN, RSTOPMODE;
input        CEA, CEB, CEC, CEM, CEP, CED, CECARRYIN, CEOPMODE;

output [17:0] BCOUT;
output [47:0] PCOUT, P;
output [35:0] M;
output        CARRYOUT, CARRYOUTF;

wire [17:0] B0_IN, B0_OUT, A0_OUT, D_OUT, B1_IN, B1_OUT, A1_OUT;
wire [35:0] M_IN, M_OUT;
wire [47:0] C_OUT, P_OUT;
wire        CYI_IN, CYI_OUT, CYO_OUT;
wire [7:0]  OPMODE_REG;
reg  [17:0] Pre_Add_Sub_Out;
reg         CYO_IN;
reg  [47:0] X_MUX, Z_MUX, Post_Add_Sub_Out;

Comb_Seq_Mux #(.WIDTH(18),.RSTTYPE(RSTTYPE),.SEL(DREG))       D_REG      (CLK,RSTD,D,CED,D_OUT);
Comb_Seq_Mux #(.WIDTH(18),.RSTTYPE(RSTTYPE),.SEL(B0REG))      B0_REG     (CLK,RSTB,B0_IN,CEB,B0_OUT);
Comb_Seq_Mux #(.WIDTH(18),.RSTTYPE(RSTTYPE),.SEL(A0REG))      A0_REG     (CLK,RSTA,A,CEA,A0_OUT);
Comb_Seq_Mux #(.WIDTH(48),.RSTTYPE(RSTTYPE),.SEL(CREG))       C_REG      (CLK,RSTC,C,CEC,C_OUT);
Comb_Seq_Mux #(.WIDTH(18),.RSTTYPE(RSTTYPE),.SEL(B1REG))      B1_REG     (CLK,RSTB,B1_IN,CEB,B1_OUT);
Comb_Seq_Mux #(.WIDTH(18),.RSTTYPE(RSTTYPE),.SEL(A1REG))      A1_REG     (CLK,RSTA,A0_OUT,CEA,A1_OUT);
Comb_Seq_Mux #(.WIDTH(36),.RSTTYPE(RSTTYPE),.SEL(MREG))       M_REG      (CLK,RSTM,M_IN,CEM,M_OUT);
Comb_Seq_Mux #(.WIDTH(01),.RSTTYPE(RSTTYPE),.SEL(CARRYINREG)) CYI_REG    (CLK,RSTCARRYIN,CYI_IN,CECARRYIN,CYI_OUT);
Comb_Seq_Mux #(.WIDTH(01),.RSTTYPE(RSTTYPE),.SEL(CARRYINREG)) CYO_REG    (CLK,RSTCARRYIN,CYO_IN,CECARRYIN,CYO_OUT);
Comb_Seq_Mux #(.WIDTH(48),.RSTTYPE(RSTTYPE),.SEL(PREG))       P_REG      (CLK,RSTP,Post_Add_Sub_Out,CEP,P_OUT);
Comb_Seq_Mux #(.WIDTH(08),.RSTTYPE(RSTTYPE),.SEL(OPMODEREG))  Opmode_Reg (CLK,RSTOPMODE,OPMODE,CEOPMODE,OPMODE_REG);

assign B0_IN = (B_INPUT == "DIRECT")? B : (B_INPUT == "CASCADE")? BCIN : 0;
assign B1_IN = (OPMODE_REG[4])? Pre_Add_Sub_Out : B0_OUT;
assign BCOUT = B1_OUT;
assign M_IN = A1_OUT * B1_OUT;
assign CYI_IN = (CARRYINSEL == "OPMODE5")? OPMODE_REG[5] : (CARRYINSEL == "CARRYIN")? CARRYIN : 0;
assign PCOUT = P_OUT;
assign P = P_OUT;
assign M = ~(~M_OUT); // buf(M,M_OUT);
assign CARRYOUT = CYO_OUT;
assign CARRYOUTF = CYO_OUT;

always @(*) begin
    if (OPMODE_REG[6])
        Pre_Add_Sub_Out = D_OUT - B0_OUT;
    else
        Pre_Add_Sub_Out = D_OUT + B0_OUT;
end

always @(*) begin
    case (OPMODE_REG[1:0])
        2'b00 : X_MUX = 0;
        2'b01 : X_MUX = {{12{1'b0}},M_OUT};
        2'b10 : X_MUX = P_OUT;
        2'b11 : X_MUX = {D_OUT[11:0],A1_OUT,B1_OUT};
    endcase
end

always @(*) begin
    case (OPMODE_REG[3:2])
        2'b00 : Z_MUX = 0;
        2'b01 : Z_MUX = PCIN;
        2'b10 : Z_MUX = P_OUT;
        2'b11 : Z_MUX = C_OUT;
    endcase
end

always @(*) begin
    if (OPMODE_REG[7])
        {CYO_IN,Post_Add_Sub_Out} = Z_MUX - (X_MUX + CYI_OUT);
    else
        {CYO_IN,Post_Add_Sub_Out} = Z_MUX + (X_MUX + CYI_OUT);
end
    
endmodule