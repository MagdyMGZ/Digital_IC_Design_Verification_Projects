module Data_Memory (
    input       wire                    clk,
    input       wire                    areset,
    input       wire                    WE,
    input       wire        [31:0]      A,
    input       wire        [31:0]      WD,
    output      wire        [31:0]      RD
);

integer i;
reg     [31:0]      data_memory     [63:0];

assign RD = data_memory[A];

always @(posedge clk or negedge areset) begin
    if (!areset) begin
        for (i = 0 ; i < 64 ; i = i + 1) begin
            data_memory[i] <= 0;
        end
    end
    else begin
        if (WE) begin
            data_memory[A] <= WD;
        end
    end
end

endmodule