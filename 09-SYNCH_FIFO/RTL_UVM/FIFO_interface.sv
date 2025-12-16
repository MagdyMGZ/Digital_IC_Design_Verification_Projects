interface FIFO_if ();
    parameter  FIFO_WIDTH = 16;
    parameter  FIFO_DEPTH = 8;

    logic clk;
    logic [FIFO_WIDTH-1:0] data_in;
    logic wr_en, rd_en, rst_n;
    logic [FIFO_WIDTH-1:0] data_out;
    logic full, almostfull, empty, almostempty, overflow, underflow, wr_ack;

    initial begin
        clk = 0;
        forever begin
            #5 clk = ~clk;
        end
    end

    clocking cb_driver @(posedge clk);
        default output #1step;
        output data_in, wr_en, rd_en, rst_n; 
    endclocking

    clocking cb_monitor @(posedge clk);
        default input #0;
        input data_in, wr_en, rd_en, rst_n, data_out, full, almostfull, empty, almostempty, overflow, underflow, wr_ack;
    endclocking
endinterface

/*

`timescale 1ns/1ns

interface FIFO_if ();
    parameter  FIFO_WIDTH = 16;
    parameter  FIFO_DEPTH = 8;
    // Signals Declaration
    logic clk;
    logic [FIFO_WIDTH-1:0] data_in;
    logic wr_en;
    logic rd_en;
    logic rst_n;
    logic [FIFO_WIDTH-1:0] data_out;
    logic full;
    logic almostfull;
    logic empty;
    logic almostempty;
    logic overflow;
    logic underflow;
    logic wr_ack;

    // Clock Generation
    initial begin
        clk = 0;
        forever begin
            #1 clk = ~clk;
        end
    end

    // Clocking Blocks is triggered in Observed Region
    // 1st Clock Cycle Drive x and Monitor x
    // Driving done at #1step after the previous posedge in Postponed Region of next timestep in the next #1 make 9ns Setup slack before the next posedge
    // Monitoring done at #0 the corresponding (inputs/outputs) at the Observed Region of the current timestep
    
    // Clocking Blocking for Synchronization Between Driver and DUT
    clocking cb_driver @(posedge clk);
        default output #1step;
        output data_in, wr_en, rd_en, rst_n;  // Driven Output from Driver Into the DUT (write-only, can't be sampled)
    endclocking

    // Clocking Blocking for Synchronization Between DUT & Monitors
    clocking cb_monitor @(posedge clk);
        default input #0;
        input data_in, wr_en, rd_en, rst_n, data_out, full, almostfull, empty, almostempty, overflow, underflow, wr_ack;
        // Sampled Inputs at Monitor from the DUT (read-only, can be sampled)
    endclocking
endinterface

*/