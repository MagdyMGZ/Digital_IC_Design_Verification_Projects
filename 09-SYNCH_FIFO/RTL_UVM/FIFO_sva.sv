module FIFO_sva #(parameter  FIFO_WIDTH = 16 ,
                  parameter  FIFO_DEPTH = 8,
				  localparam max_fifo_addr = $clog2(FIFO_DEPTH))     
                (       
                        input logic clk,
                        input logic [FIFO_WIDTH-1:0] data_in,
                        input logic wr_en,
                        input logic rd_en,
                        input logic rst_n,
                        input logic [FIFO_WIDTH-1:0] data_out,
                        input logic full,
                        input logic almostfull,
                        input logic empty,
                        input logic almostempty,
                        input logic overflow,
                        input logic underflow,
                        input logic wr_ack, 
                        input bit [max_fifo_addr:0]   count, 
                        input bit [max_fifo_addr-1:0] wr_ptr,
                        input bit [max_fifo_addr-1:0] rd_ptr
                );

// Assertions to the DUT

	// Assertions for Combinational Outputs
	always_comb begin
		if (!rst_n) begin
			RST_assertion : assert final (~wr_ptr && ~rd_ptr && ~count && empty && !full && !almostempty && !almostfull) else $display("RST_assertion fail");
			RST_cover     : cover  final (~wr_ptr && ~rd_ptr && ~count && empty && !full && !almostempty && !almostfull); //  $display("RST_assertion pass");
		end
		if ((count == 0) && $time > 0ns) begin
			EMPTY_assertion : assert final (empty && !full && !almostempty && !almostfull) else $display("EMPTY_assertion fail");
			EMPTY_cover     : cover final (empty && !full && !almostempty && !almostfull); //   $display("EMPTY_assertion Pass");
		end
		if (count == 1) begin
			ALMOSTEMPTY_assertion : assert final (!empty && !full && almostempty && !almostfull) else $display("ALMOSTFULL_assertion fail");
			ALMOSTEMPTY_cover     : cover final  (!empty && !full && almostempty && !almostfull); //  $display("ALMOSTFULL_assertion Pass");
		end
		if (count == FIFO_DEPTH-1) begin
			ALMOSTFULL_assertion : assert final (!empty && !full && !almostempty && almostfull) else $display("ALMOSTFULL_assertion fail");
			ALMOSTFULL_cover     : cover final  (!empty && !full && !almostempty && almostfull); //  $display("ALMOSTEMPTY_assertion Pass");
		end
		if (count == FIFO_DEPTH) begin
			FULL_assertion : assert final (!empty && full && !almostempty && !almostfull) else $display("FULL_assertion fail");
			FULL_cover     : cover final (!empty && full && !almostempty && !almostfull); //   $display("FULL_assertion Pass");
		end
	end

	// Assertions for Overflow and Underflow
	property OVERFLOW_FIFO;
		@(posedge clk) disable iff (!rst_n) (full & wr_en) |=> (overflow);
	endproperty

	property UNDERFLOW_FIFO;
		@(posedge clk) disable iff (!rst_n) (empty && rd_en) |=> (underflow);
	endproperty

	// Assertions for wr_ack
	property WR_ACK_HIGH;
		@(posedge clk) disable iff (!rst_n) (wr_en && (count < FIFO_DEPTH) && !full) |=> (wr_ack);
	endproperty

	property WR_ACK_LOW;
		@(posedge clk) disable iff (!rst_n) (wr_en && full) |=> (!wr_ack);
	endproperty

	// Assertions for The Counter
	property COUNT_0;
		@(posedge clk) (!rst_n) |=> (count == 0);
	endproperty

	property COUNT_INC_10;
		@(posedge clk) disable iff (!rst_n) (({wr_en, rd_en} == 2'b10) && !full) |=> (count == $past(count) + 1);
	endproperty

	property COUNT_INC_01;
		@(posedge clk) disable iff (!rst_n) (({wr_en, rd_en} == 2'b01) && !empty) |=> (count == $past(count) - 1);
	endproperty

	property COUNT_INC_11_WR;
		@(posedge clk) disable iff (!rst_n) (({wr_en, rd_en} == 2'b11) && empty) |=> (count == $past(count) + 1);
	endproperty

	property COUNT_INC_11_RD;
		@(posedge clk) disable iff (!rst_n) (({wr_en, rd_en} == 2'b11) && full) |=> (count == $past(count) - 1);
	endproperty

	property COUNT_LAT;
		@(posedge clk) disable iff (!rst_n) ((({wr_en, rd_en} == 2'b01) && empty) || (({wr_en, rd_en} == 2'b10) && full)) |=> (count == $past(count));
	endproperty

	// Assertions for Pointers
	property PTR_RST;
		@(posedge clk) (!rst_n) |=> (~rd_ptr && ~wr_ptr);
	endproperty

	property RD_PTR;
		@(posedge clk) disable iff (!rst_n) (rd_en && (count != 0) && !empty) |=> (rd_ptr == ($past(rd_ptr) + 1) % FIFO_DEPTH);
	endproperty

	property WR_PTR;
		@(posedge clk) disable iff (!rst_n) (wr_en && (count < FIFO_DEPTH) && !full) |=> (wr_ptr == ($past(wr_ptr) + 1) % FIFO_DEPTH);
	endproperty

	// Pointer wraparound assertion for write_ptr
 	property WR_PTR_wraparound;
 		@(posedge clk) disable iff (!rst_n) (wr_en && !full && (wr_ptr == FIFO_DEPTH-1)) |=> (~wr_ptr) [->1];
	endproperty

	// Pointer wraparound assertion for read_ptr
	property RD_PTR_wraparound;
 		@(posedge clk) disable iff (!rst_n) (rd_en && !empty && (rd_ptr == FIFO_DEPTH-1)) |=> (~rd_ptr) [->1];
	endproperty

	// Counter wraparound assertion
	property COUNT_wraparound;
		@(posedge clk) disable iff (!rst_n) (wr_en && (count == FIFO_DEPTH) && full) |=> (~count) [->1];
	endproperty

	// Pointer threshold assertion for write_ptr
	property WR_PTR_threshold;
		@(posedge clk) disable iff (!rst_n) (wr_ptr < FIFO_DEPTH);
	endproperty

	// Pointer threshold assertion for read_ptr
	property RD_PTR_threshold;
		@(posedge clk) disable iff (!rst_n) (rd_ptr < FIFO_DEPTH);
	endproperty

	// Counter threshold assertion
	property COUNT_threshold;
		@(posedge clk) disable iff (!rst_n) (count <= FIFO_DEPTH);
	endproperty

	// Assert Properties
	OVERFLOW_assertion          : assert property (OVERFLOW_FIFO)     else $display("OVERFLOW_assertion fail");
	UNDERFLOW_assertion         : assert property (UNDERFLOW_FIFO)    else $display("UNDERFLOW_assertion fail");
	WR_ACK_HIGH_assertion       : assert property (WR_ACK_HIGH)       else $display("WR_ACK_HIGH_assertion fail");
	WR_ACK_LOW_assertion        : assert property (WR_ACK_LOW)        else $display("WR_ACK_LOW_assertion fail");
	COUNTER_INC_10_assertion    : assert property (COUNT_INC_10)      else $display("COUNTER_INC_WR_assertion fail");
	COUNTER_INC_01_assertion    : assert property (COUNT_INC_01)      else $display("COUNTER_INC_WR_assertion fail");
	COUNTER_INC_11_WR_assertion : assert property (COUNT_INC_11_WR)   else $display("COUNTER_INC_WR_assertion fail");
	COUNTER_INC_11_RD_assertion : assert property (COUNT_INC_11_RD)   else $display("COUNTER_INC_WR_assertion fail");
	COUNTER_LAT_assertion       : assert property (COUNT_LAT)         else $display("COUNTER_LAT_assertion fail");
	RD_PTR_assertion            : assert property (RD_PTR)            else $display("RD_PTR_asssertion fail");
	WR_PTR_assertion            : assert property (WR_PTR)            else $display("WR_PTR_asssertion fail");
	WR_PTR_wraparound_assertion : assert property (WR_PTR_wraparound) else $display("WR_PTR_wraparound_assertion fail");
	RD_PTR_wraparound_assertion : assert property (RD_PTR_wraparound) else $display("RD_PTR_wraparound_assertion fail");
	COUNT_wraparound_assertion  : assert property (COUNT_wraparound)  else $display("COUNT_wraparound_assertion fail");
	WR_PTR_threshold_assertion  : assert property (WR_PTR_threshold)  else $display("WR_PTR_threshold_assertion fail");
	RD_PTR_threshold_assertion  : assert property (RD_PTR_threshold)  else $display("RD_PTR_threshold_assertion fail");
	COUNT_threshold_assertion   : assert property (COUNT_threshold)   else $display("COUNT_threshold_assertion fail");

	// Cover Properties
	OVERFLOW_cover          : cover property (OVERFLOW_FIFO); //        $display("OVERFLOW_assertion Pass");
	UNDERFLOW_cover         : cover property (UNDERFLOW_FIFO); //       $display("UNDERFLOW_assertion Pass");
	WR_ACK_HIGH_cover       : cover property (WR_ACK_HIGH); //          $display("WR_ACK_HIGH_assertion Pass");
	WR_ACK_LOW_cover        : cover property (WR_ACK_LOW); //           $display("WR_ACK_LOW_assertion Pass");
	COUNTER_INC_10_cover    : cover property (COUNT_INC_10); //         $display("COUNTER_INC_WR_assertion Pass");
	COUNTER_INC_01_cover    : cover property (COUNT_INC_01); //         $display("COUNTER_INC_WR_assertion Pass");
	COUNTER_INC_11_WR_cover : cover property (COUNT_INC_11_WR); //      $display("COUNTER_INC_WR_assertion Pass");
	COUNTER_INC_11_RD_cover : cover property (COUNT_INC_11_RD); //      $display("COUNTER_INC_WR_assertion Pass");
	COUNTER_LAT_cover       : cover property (COUNT_LAT); //            $display("COUNTER_LAT_assertion Pass");
	RD_PTR_cover            : cover property (RD_PTR); //               $display("RD_PTR_asssertion pass");
	WR_PTR_cover            : cover property (WR_PTR); //               $display("WR_PTR_asssertion pass");
	WR_PTR_wraparound_cover : cover property (WR_PTR_wraparound); //    $display("WR_PTR_wraparound_assertion pass");
	RD_PTR_wraparound_cover : cover property (RD_PTR_wraparound); //    $display("RD_PTR_wraparound_assertion pass");
	COUNT_wraparound_cover  : cover property (COUNT_wraparound); //     $display("COUNT_wraparound_assertion pass");
	WR_PTR_threshold_cover  : cover property (WR_PTR_threshold); //     $display("WR_PTR_threshold_assertion pass");
	RD_PTR_threshold_cover  : cover property (RD_PTR_threshold); //     $display("RD_PTR_threshold_assertion pass");
	COUNT_threshold_cover   : cover property (COUNT_threshold); //      $display("COUNT_threshold_assertion pass");

endmodule
