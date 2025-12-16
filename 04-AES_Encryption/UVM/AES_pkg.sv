package AES_pkg;
`timescale 1ns/1ps
localparam TESTS = 1000;
localparam N  = 128;
localparam Nr = 10;
localparam Nk = 4;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "AES_config.svh"
`include "AES_sequence_item.svh"
`include "AES_sequencer.svh"
`include "AES_sequence.svh"
`include "AES_driver.svh"
`include "AES_monitor.svh"
`include "AES_agent.svh"
`include "AES_scoreboard.svh"
`include "AES_collector.svh"
`include "AES_env.svh"
`include "AES_test.svh"
endpackage