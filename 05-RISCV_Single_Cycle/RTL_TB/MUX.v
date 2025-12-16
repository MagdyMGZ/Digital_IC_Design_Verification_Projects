module MUX (
    input       wire        [31:0]      In1,
    input       wire        [31:0]      In2,
    input       wire                    Sel,
    output      wire        [31:0]      Out
);

assign Out = (Sel)? In2 : In1;

endmodule