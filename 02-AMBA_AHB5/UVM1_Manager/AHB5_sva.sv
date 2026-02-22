import shared_pkg::*;
module AHB5_sva (
	input       logic                                HCLK,
    input       logic                                HRESETn,
    input       logic                                HSELx,
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

logic invalid_trans;

assign invalid_trans = ((HADDR[OFFSET-1:0] > (MEM_DEPTH-1)) || ((8 << HSIZE) > DATA_WIDTH));

always_comb begin
	if (!HRESETn) begin
		assert__HRESETn_property : assert final ((~HRDATA) && (!HREADYOUT) && (!HRESP));
		cover__HRESETn_property  : cover  final ((~HRDATA) && (!HREADYOUT) && (!HRESP));
	end
end

property HREADYOUT_property;
    @(posedge HCLK) disable iff (!HRESETn) (HSELx && HREADY && (HTRANS == SEQ || HTRANS == NONSEQ)) |-> ##2 ($rose(HREADYOUT) || HREADYOUT);
endproperty

assert property (HREADYOUT_property);
cover property (HREADYOUT_property);

property NOT_HREADYOUT_property;
    @(posedge HCLK) disable iff (!HRESETn) (!HSELx || !HREADY || (HTRANS == IDLE || HTRANS == BUSY)) |-> ##2 ($fell(HREADYOUT) || !HREADYOUT);
endproperty

assert property (NOT_HREADYOUT_property);
cover property (NOT_HREADYOUT_property);

property HRESP1_property;
    @(posedge HCLK) disable iff (!HRESETn) (($rose(invalid_trans) || invalid_trans) && HREADY && HSELx) |-> ##2 ((HRESP || $rose(HRESP)) && ($rose(HREADYOUT) || HREADYOUT));
endproperty

assert property (HRESP1_property);
cover property (HRESP1_property);

property HRESP0_property;
    @(posedge HCLK) disable iff (!HRESETn) (($fell(invalid_trans) || !invalid_trans) && HREADY && HSELx)  |-> ##2 (!HRESP || $fell(HRESP));
endproperty

assert property (HRESP0_property);
cover property (HRESP0_property);

endmodule