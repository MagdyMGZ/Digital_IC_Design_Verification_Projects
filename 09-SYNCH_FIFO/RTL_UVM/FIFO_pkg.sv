package FIFO_pkg;
`timescale 1ns/1ps
localparam TESTS = 10000;
parameter  FIFO_WIDTH = 16;
parameter  FIFO_DEPTH = 8;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "FIFO_config.svh"
`include "FIFO_sequence_item.svh"
`include "FIFO_sequencer.svh"
`include "FIFO_sequence.svh"
`include "FIFO_driver.svh"
`include "FIFO_monitor.svh"
`include "FIFO_agent.svh"
`include "FIFO_scoreboard.svh"
`include "FIFO_collector.svh"
`include "FIFO_env.svh"
`include "FIFO_test.svh"
endpackage