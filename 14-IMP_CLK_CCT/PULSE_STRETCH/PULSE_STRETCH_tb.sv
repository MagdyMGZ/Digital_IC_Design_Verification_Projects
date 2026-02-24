module PULSE_STRETCH_tb ();

parameter STRETCH_RATIO = 4;

logic       i_clk;
logic       i_rst_n;
logic       i_pulse;
logic       o_pulse_stretched;
    
PULSE_STRETCH #(.STRETCH_RATIO(STRETCH_RATIO)) DUT (.*);

initial begin
    i_clk = 0;
    forever begin
        #1 i_clk = ~i_clk;
    end
end

initial begin
    i_rst_n = 0; 
    @(negedge i_clk);
    i_rst_n = 1;

    repeat (100) begin
        i_pulse = 0;
        @(negedge i_clk);
        i_pulse = 1;
        @(negedge i_clk);
        i_pulse = 0;

        repeat (4) @(negedge i_clk);
    end

    $stop;
end

endmodule