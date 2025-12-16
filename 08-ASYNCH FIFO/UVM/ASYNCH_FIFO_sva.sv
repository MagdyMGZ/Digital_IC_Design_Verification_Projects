module ASYNCH_FIFO_sva #(
	parameter  FIFO_WIDTH = 4,
	parameter  FIFO_DEPTH = 8,
	localparam ADDR_WIDTH = $clog2(FIFO_DEPTH)
) (       
    input       logic                                i_rst_n,
    input       logic                                i_wclk,
    input       logic                                i_wen,
    input       logic        [FIFO_WIDTH-1:0]        i_wdata,
    input       logic                                i_rclk,
    input       logic                                i_ren,
    input       logic                                o_full,
    input       logic                                o_empty,
    input       logic        [FIFO_WIDTH-1:0]        o_rdata,
	input		logic	     [ADDR_WIDTH:0]		     wr_ptr,
	input		logic		 [ADDR_WIDTH:0]		     rd_ptr
);

always_comb begin
	if (!i_rst_n) begin
		RST_ASSERTION: assert final (!o_full && o_empty && ~wr_ptr && ~rd_ptr);
		RST_COVER:     cover  final (!o_full && o_empty && ~wr_ptr && ~rd_ptr);
	end
end

sequence FULL_CONDITION;
	((wr_ptr[ADDR_WIDTH] != $past(rd_ptr[ADDR_WIDTH], 1)) && 
	 (wr_ptr[ADDR_WIDTH-1:0] == $past(rd_ptr[ADDR_WIDTH-1:0], 1)));
endsequence

sequence EMPTY_CONDITION;
	(rd_ptr == $past(wr_ptr, 1));
endsequence

property full_cond_property;
	@(posedge i_wclk) disable iff (!i_rst_n) FULL_CONDITION |-> (o_full || $rose(o_full));
endproperty

property empty_cond_property;
	@(posedge i_rclk) disable iff (!i_rst_n) EMPTY_CONDITION |-> (o_empty || $rose(o_empty));
endproperty

property wr_ptr_cond_property;
	@(posedge i_wclk) disable iff (!i_rst_n) (i_wen && !o_full) |=> (wr_ptr == $past(wr_ptr) + 1'b1);
endproperty

property rd_ptr_cond_property;
	@(posedge i_rclk) disable iff (!i_rst_n) (i_ren && !o_empty) |=> (rd_ptr == $past(rd_ptr) + 1'b1);
endproperty

full_cond_assertion : assert property (full_cond_property);
full_cond_cover: cover property (full_cond_property);

empty_cond_assertion : assert property (empty_cond_property);
empty_cond_cover: cover property (empty_cond_property);

wr_ptr_cond_assertion : assert property (wr_ptr_cond_property);
wr_ptr_cond_cover: cover property (wr_ptr_cond_property);

rd_ptr_cond_assertion : assert property (rd_ptr_cond_property);
rd_ptr_cond_cover: cover property (rd_ptr_cond_property);

endmodule
