//////////////////////////////////////////////////////////////////
// Author      : Magdy Ahmed Abbas
// File        : CLK_DIV.sv
// Description : Clock Divider for any integer number even or odd
//////////////////////////////////////////////////////////////////
module CLK_DIV (
    input		logic        i_clk,
    input		logic        i_rst_n,
    input		integer      i_div_ratio,
    output      logic        o_clk
);

integer counter_even;
integer counter_odd;

logic o_clk_even;
logic o_clk_odd;
logic o_clk_delayed;

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        counter_even <= 0;
        o_clk_even <= 0;
    end
    else begin
        if (counter_even == (i_div_ratio-1)) begin
            counter_even <= 0;
            o_clk_even <= 0;
        end
        else begin
            counter_even <= counter_even + 1;
            if (counter_even == ((i_div_ratio/2)-1))
                o_clk_even <= !o_clk_even;
        end
    end
end

always @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        counter_odd <= 0;
        o_clk_odd <= 0;
    end
    else begin
        if (counter_odd == (i_div_ratio-1)) begin
            counter_odd <= 0;
            o_clk_odd <= 0;
        end
        else begin
            counter_odd <= counter_odd + 1;
            if (counter_odd == ((i_div_ratio-1)/2))
                o_clk_odd <= !o_clk_odd;
        end
    end
end

always @(negedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        o_clk_delayed <= 0;
    end
    else begin
        o_clk_delayed <= o_clk_odd;
    end
end

assign o_clk = ((i_div_ratio % 2) == 0)? o_clk_even : (o_clk_odd | o_clk_delayed);

endmodule