package adder_package;
	localparam TESTS = 1000;   
	`include "adder_trans.svh"      // Sequence item
	`include "adder_generator.svh"  // Sequence
	`include "adder_driver.svh"     // Driver
	`include "monitor_output.svh"   // Monitor Output
	`include "monitor_input.svh"    // Monitor Input
	`include "adder_checker.svh"    // Scoreboard
	`include "adder_collector.svh"  // Coverage Collector
endpackage
