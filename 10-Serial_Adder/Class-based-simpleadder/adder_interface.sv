`timescale 1ns/1ns

interface adder_if ();
    // Signals Declaration
    logic clk, en_i, ina, inb;
    logic en_o, out;

    // Clock Generation
    initial begin
        clk = 0;
        forever begin
            #10 clk = ~clk;
        end
    end

    // Clocking Blocks is triggered in Observed Region
    // 1st Clock Cycle Drive x and Monitor x
    // Driving done at #1step after the previous posedge in Postponed Region of next timestep in the next #1 make 9ns Setup slack before the next posedge
    // Monitoring done at #0 the corresponding (inputs/outputs) at the Observed Region of the current timestep
    
    // Clocking Blocking for Synchronization Between Driver and DUT
    clocking cb_driver @(posedge clk);
        default output #1step;
        output en_i, ina, inb;  // Driven Output from Driver Into the DUT (write-only, can't be sampled)
    endclocking

    // Clocking Blocking for Synchronization Between DUT & Monitors
    clocking cb_monitor @(posedge clk);
        default input #0;
        input en_o, out, en_i, ina, inb;
        // Sampled Inputs at Monitor from the DUT (read-only, can be sampled) 
    endclocking
endinterface