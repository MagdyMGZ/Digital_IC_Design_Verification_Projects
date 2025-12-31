module PULSE_GEN_tb ();

logic i_clk;
logic i_rst_n;
logic i_level_signal;
logic o_posedge_pls_gen;
logic o_negedge_pls_gen;
logic o_both_edge_pls_gen;

PULSE_GEN DUT (.*);

initial begin
    i_clk = 0;
    forever begin
        #5 i_clk = !i_clk;
    end
end

initial begin
    i_rst_n = 0;
    @(negedge i_clk);
    i_rst_n = 1;

    repeat (1000) begin
        @(negedge i_clk);
        i_level_signal = $random;
    end

    $stop;
end
    
endmodule