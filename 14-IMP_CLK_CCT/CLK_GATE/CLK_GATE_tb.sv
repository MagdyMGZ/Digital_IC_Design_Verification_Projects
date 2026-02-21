module CLK_GATE_tb ();

logic i_clk;
logic i_clk_en;
logic o_clk_gated;
    
CLK_GATE DUT (.*);

initial begin
    i_clk = 0;
    forever begin
        #10 i_clk = ~i_clk;
    end
end

initial begin
    // Glitchs EN
    @(negedge i_clk);
    repeat (500) begin
        i_clk_en = 0;
        #1 
        i_clk_en = 1;
        #1
        i_clk_en = 0;
    end

    // Stable EN
    @(negedge i_clk);
    repeat (500) begin
        @(negedge i_clk);
        i_clk_en = $random;
    end

    $stop;
end

endmodule