package APB4_pkg;
localparam TESTS = 1000;
parameter  DATA_WIDTH = 32;
parameter  ADDR_WIDTH = 32;
parameter  MEM_DEPTH  = 64;
localparam STRB_WIDTH = DATA_WIDTH/8;
typedef enum logic {read = 0 , write = 1} type_e;
typedef enum logic {regfile_slv0 = 0 , memory_slv1 = 1} slv_sel;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "APB4_config.svh"
`include "APB4_sequence_item.svh"
`include "APB4_sequencer.svh"
`include "APB4_sequence.svh"
`include "APB4_driver.svh"
`include "APB4_monitor.svh"
`include "APB4_agent.svh"
`include "APB4_scoreboard.svh"
`include "APB4_collector.svh"
`include "APB4_env.svh"
`include "APB4_test.svh"
endpackage