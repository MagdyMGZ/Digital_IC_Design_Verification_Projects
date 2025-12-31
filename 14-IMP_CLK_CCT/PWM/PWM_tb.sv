module PWM_tb ();

parameter RESOLUTION = 4;

logic                  i_clk;
logic                  i_rst_n;
logic [RESOLUTION-1:0] i_duty_cycle;
logic                  o_clk_pwm;

PWM #(.RESOLUTION(RESOLUTION)) DUT (.*);

initial begin
    i_clk = 0;
    forever begin
        #5 i_clk = ~i_clk;
    end
end

initial begin
    i_rst_n = 0;
    @(negedge i_clk);
    i_rst_n = 1;

    i_duty_cycle = 12;
    repeat (100) @(negedge i_clk);

    $stop;
end

endmodule