module Comb_Seq_Mux (CLK,RST,IN,CE,OUT);

parameter WIDTH   = 18;
parameter RSTTYPE = "SYNC";
parameter SEL     = 1;

reg [WIDTH-1:0] OUT_REG;

input [WIDTH-1:0] IN;
input RST, CLK, CE;
output [WIDTH-1:0] OUT;

generate

case (RSTTYPE)
    "SYNC" : begin
        always @(posedge CLK) begin
            if (RST)
                OUT_REG <= 0;
            else begin
                if (CE)
                    OUT_REG <= IN;
            end
        end
    end
    "ASYNC" : begin
        always @(posedge CLK or posedge RST) begin
            if (RST)
                OUT_REG <= 0;
            else begin
                if (CE)
                    OUT_REG <= IN;
            end
        end
    end
endcase

endgenerate

assign OUT = (SEL)? OUT_REG : IN;
    
endmodule