package ASYNCH_FIFO_pkg;
`timescale 1ns/1ps
parameter  FIFO_WIDTH = 4;
parameter  FIFO_DEPTH = 8;
localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);
localparam TESTS = 10000;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "ASYNCH_FIFO_config.svh"
`include "ASYNCH_FIFO_sequence_item.svh"
`include "ASYNCH_FIFO_sequence.svh"
`include "ASYNCH_FIFO_sequencer.svh"
`include "ASYNCH_FIFO_driver.svh"
`include "ASYNCH_FIFO_monitor.svh"
`include "ASYNCH_FIFO_agent.svh"
`include "ASYNCH_FIFO_scoreboard.svh"
`include "ASYNCH_FIFO_collector.svh"
`include "ASYNCH_FIFO_env.svh"
`include "ASYNCH_FIFO_test.svh"
endpackage