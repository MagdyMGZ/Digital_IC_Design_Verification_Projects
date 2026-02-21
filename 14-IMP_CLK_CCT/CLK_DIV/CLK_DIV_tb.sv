module CLK_DIV_tb ();

logic	i_clk;
logic   i_rst_n;
integer i_div_ratio;
logic   o_clk;

CLK_DIV DUT (.*);

initial begin
	i_clk = 0;
	forever begin
		#1 i_clk = ~i_clk;
	end
end

initial begin
	/////// TEST 1 ///////
	i_rst_n = 0;
	@(negedge i_clk);
	i_rst_n = 1;

	i_div_ratio = 5;  // ODD
	repeat (100) @(negedge i_clk);

	/////// TEST 2 ///////
	i_rst_n = 0;
	@(negedge i_clk);
	i_rst_n = 1;

	i_div_ratio = 24; // EVEN
	repeat (100) @(negedge i_clk);

	/////// TEST 3 ///////
	i_rst_n = 0;
	@(negedge i_clk);
	i_rst_n = 1;

	i_div_ratio = 17; // ODD
	repeat (100) @(negedge i_clk);

	/////// TEST 4 ///////
	i_rst_n = 0;
	@(negedge i_clk);
	i_rst_n = 1;

	i_div_ratio = 36; // EVEN
	repeat (100) @(negedge i_clk);

	$stop;
end

endmodule