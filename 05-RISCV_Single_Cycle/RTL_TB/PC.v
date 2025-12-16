module PC (
    input       wire                    areset,
    input       wire                    clk,
    input       wire        [31:0]      PCNext,
    output      reg         [31:0]      PC
);

always @(posedge clk or negedge areset) begin
    if (!areset) begin
        PC <= 0;
    end
    else begin
        PC <= PCNext;
    end
end
    
endmodule