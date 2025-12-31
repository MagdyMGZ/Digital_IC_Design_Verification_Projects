////////////////////////////////////////////////////////////////////////////
// Author      : Magdy Ahmed Abbas
// File        : PWM.sv
// Description : Pulse Width Modulation with Parameterized Resolution
////////////////////////////////////////////////////////////////////////////
module PWM #(
    parameter RESOLUTION = 4 
    // The Minimum incremental duty cycle step is (1/2^R)
) (
    input       logic                   i_clk,
    input       logic                   i_rst_n,
    input       [RESOLUTION-1:0]        i_duty_cycle,
    output      logic                   o_clk_pwm
);

reg [RESOLUTION-1:0] counter;

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        counter <= 0;
        o_clk_pwm <= 0;
    end
    else begin
        counter <= counter + 1;
        if (counter < i_duty_cycle)
            o_clk_pwm <= 1;
        else
            o_clk_pwm <= 0;
    end
end

endmodule