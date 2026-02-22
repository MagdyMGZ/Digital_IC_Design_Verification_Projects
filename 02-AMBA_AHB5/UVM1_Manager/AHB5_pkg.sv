package AHB5_pkg;
    localparam TESTS = 10000;
    import uvm_pkg::*;
    import shared_pkg::*;
    `include "uvm_macros.svh"
    `include "AHB5_config.svh"
    `include "AHB5_sequence_item.svh"
    `include "AHB5_sequencer.svh"
    `include "AHB5_sequence.svh"
    `include "AHB5_driver.svh"
    `include "AHB5_monitor.svh"
    `include "AHB5_agent.svh"
    `include "AHB5_scoreboard.svh"
    `include "AHB5_collector.svh"
    `include "AHB5_env.svh"
    `include "AHB5_test.svh"
endpackage