`timescale 1ns/1ns

import temp_shared_pkg::*;

interface temp_if ();

logic clk;

initial begin
    clk = 0;
    forever begin
        #(CLK_PERIOD/2) clk = ~clk;
    end
end

endinterface