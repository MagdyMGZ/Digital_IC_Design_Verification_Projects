interface ASYNCH_FIFO_if ();
    parameter  FIFO_WIDTH = 4;
    parameter  FIFO_DEPTH = 8;
    // Signals Declaration
    logic                  i_rst_n;
    logic                  i_wclk;
    logic                  i_wen;
    logic [FIFO_WIDTH-1:0] i_wdata;
    logic                  i_rclk;
    logic                  i_ren;
    logic                  o_full;
    logic                  o_empty;
    logic [FIFO_WIDTH-1:0] o_rdata;

    logic                  o_full_gold;
    logic                  o_empty_gold;
    logic [FIFO_WIDTH-1:0] o_rdata_gold;

    // Clock Generation
    initial begin
        i_wclk = 0;
        forever begin
            #10 i_wclk = ~i_wclk;
        end
    end

    initial begin
        i_rclk = 0;
        forever begin
            #5 i_rclk = ~i_rclk;
        end
    end

    // Clocking Blocks is triggered in Observed Region
    // 1st Clock Cycle Drive x and Monitor x
    // Driving done at #1step after the previous posedge in Postponed Region of next timestep in the next #1 make 9ns Setup slack before the next posedge
    // Monitoring done at #0 the corresponding (inputs/outputs) at the Observed Region of the current timestep
    
    // Clocking Blocking for Synchronization Between Driver and DUT
    clocking cb_driver_wr @(posedge i_wclk);
        default output #1step;
        output i_ren, i_wdata, i_wen, i_rst_n;  // Driven Output from Driver Into the DUT (write-only, can't be sampled)
    endclocking

    clocking cb_driver_rd @(posedge i_rclk);
        default output #1step;
        output i_ren, i_wdata, i_wen, i_rst_n;  // Driven Output from Driver Into the DUT (write-only, can't be sampled)
    endclocking

    // Clocking Blocking for Synchronization Between DUT & Monitors
    clocking cb_monitor_wr @(posedge i_wclk);
        default input #0;
        input i_ren, i_wdata, i_wen, i_rst_n, o_full, o_empty, o_rdata, o_full_gold, o_empty_gold, o_rdata_gold;
        // Sampled Inputs at Monitor from the DUT (read-only, can be sampled) 
    endclocking

    clocking cb_monitor_rd @(posedge i_rclk);
        default input #0;
        input i_ren, i_wdata, i_wen, i_rst_n, o_full, o_empty, o_rdata, o_full_gold, o_empty_gold, o_rdata_gold;
        // Sampled Inputs at Monitor from the DUT (read-only, can be sampled) 
    endclocking

endinterface