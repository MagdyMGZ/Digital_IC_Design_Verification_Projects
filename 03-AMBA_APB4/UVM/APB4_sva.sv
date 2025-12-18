module APB4_sva #(
	parameter  DATA_WIDTH = 32,
	parameter  ADDR_WIDTH = 32,
	parameter  MEM_DEPTH  = 64,
	localparam STRB_WIDTH = DATA_WIDTH/8
) (
	input       logic                               PCLK,
	input       logic                               PRESETn,
	input       logic                               TRANSFER,
	input       logic                               WRITE,
	input       logic       [ADDR_WIDTH-1:0]        ADDR,
	input       logic       [DATA_WIDTH-1:0]        WDATA,
	input       logic       [STRB_WIDTH-1:0]        STRB,
	input       logic                               READY,
	input       logic       [DATA_WIDTH-1:0]		RDATA,
	input       logic                               SLVERR,
	input		logic                  			    PSEL0, 
	input		logic                  			    PSEL1, 
	input		logic                  			    PENABLE
);

property PRESETn_property;
    @(posedge PCLK) (!PRESETn) |=> ((~RDATA) && (!READY) && (!SLVERR));
endproperty

assert property (PRESETn_property);
cover property (PRESETn_property);

property PSELx_property;
    @(posedge PCLK) disable iff(!PRESETn) $rose(TRANSFER) |=> (PSEL0 || PSEL1);
endproperty

assert property (PSELx_property);
cover property (PSELx_property);

property En_property;
    @(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) ##1 ($rose(PSEL0) || $rose(PSEL1))) |=> ($rose(PENABLE) || PENABLE);
endproperty

assert property (En_property);
cover property (En_property);

property Ready_property;
    @(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) ##1 ($rose(PSEL0) || $rose(PSEL1)) ##1 $rose(PENABLE) ##1 $rose(READY)) |=> $fell(READY) [->1];
endproperty

assert property (Ready_property);
cover property (Ready_property);

property Write_Ready_property;
    @(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) ##1 $rose(WRITE) ##2 $rose(READY)) |=> $fell(READY) [->1];
endproperty

assert property (Write_Ready_property);
cover property (Write_Ready_property);

property Read_Ready_property;
    @(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) ##1 $fell(WRITE) ##2 $rose(READY)) |=> $fell(READY) [->1];
endproperty

assert property (Read_Ready_property);
cover property (Read_Ready_property);

property PSEL0_property;
	@(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) && !ADDR[ADDR_WIDTH-1]) |=> $rose(PSEL0) [->1];
endproperty

assert property (PSEL0_property);
cover property (PSEL0_property);

property PSEL1_property;
	@(posedge PCLK) disable iff(!PRESETn) ($rose(TRANSFER) && ADDR[ADDR_WIDTH-1]) |=> $rose(PSEL1) [->1];
endproperty

assert property (PSEL1_property);
cover property (PSEL1_property);

always @(*) begin
	assert__SLVERR_property : assert final (!SLVERR);
	cover__SLVERR_property : cover final (!SLVERR);
end

endmodule