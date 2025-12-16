module Register_File (
    input       wire                    areset,
    input       wire                    clk,
    input       wire                    WE3,
    input       wire        [4:0]       A1,
    input       wire        [4:0]       A2,
    input       wire        [4:0]       A3,
    input       wire        [31:0]      WD3,
    output      wire        [31:0]      RD1,
    output      wire        [31:0]      RD2   
);

integer i;
reg     [31:0]      reg_file     [31:0];

assign RD1 = reg_file[A1];
assign RD2 = reg_file[A2];

always @(posedge clk or negedge areset) begin
    if (!areset) begin
        for (i = 0 ; i < 32 ; i = i + 1) begin
            reg_file[i] <= 0;
        end
    end
    else begin
        if (WE3) begin
            reg_file[A3] <= WD3;
        end
    end
end

endmodule