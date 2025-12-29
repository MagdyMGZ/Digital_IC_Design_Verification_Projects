import shared_pkg::*;
module AHB5_sva #(
	parameter  DATA_WIDTH   = 32,
    parameter  ADDR_WIDTH   = 32,
    parameter  HBURST_WIDTH = 3,
    parameter  MEM_DEPTH    = 64,
    localparam STRB_WIDTH   = DATA_WIDTH/8,
    localparam WORD_ADDR    = $clog2(MEM_DEPTH)
) (
	input       logic                                HCLK,
    input       logic                                HRESETn,
    input       logic                                HSEL1,
    input       logic                                HREADY,
    input       logic        [ADDR_WIDTH-1:0]        HADDR,
    input       hburst_e					         HBURST,
    input       hsize_e                              HSIZE,
    input       htrans_e                             HTRANS,
    input       logic        [DATA_WIDTH-1:0]        HWDATA,
    input       logic        [STRB_WIDTH-1:0]        HWSTRB,
    input       type_e                               HWRITE,
    input       logic        [DATA_WIDTH-1:0]        HRDATA,
    input       logic                                HREADYOUT,
    input       logic                                HRESP
);

always_comb begin
	if (!HRESETn) begin
		assert__HRESETn_property : assert final ((~HRDATA) && (!HREADYOUT) && (!HRESP));
		cover__HRESETn_property  : cover  final ((~HRDATA) && (!HREADYOUT) && (!HRESP));
	end
end

property HREADYOUT_property;
    @(posedge HCLK) disable iff (!HRESETn) (HSEL1 && HREADY && (HTRANS == SEQ || HTRANS == NONSEQ)) |=> ($rose(HREADYOUT) || HREADYOUT);
endproperty

assert property (HREADYOUT_property);
cover property (HREADYOUT_property);

property NOT_HREADYOUT_property;
    @(posedge HCLK) disable iff (!HRESETn) (!HSEL1 || !HREADY || (HTRANS == IDLE || HTRANS == BUSY)) |=> ($fell(HREADYOUT) || !HREADYOUT);
endproperty

assert property (NOT_HREADYOUT_property);
cover property (NOT_HREADYOUT_property);

always @(*) begin
	assert__HRESP_property : assert final (!HRESP);
	cover__HRESP_property : cover final (!HRESP);
end

endmodule