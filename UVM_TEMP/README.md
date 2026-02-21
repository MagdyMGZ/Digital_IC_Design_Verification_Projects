### UVM Template 

## 1st Step: Change File Names (.sv or .svh)
- You need to go through all file names and rename them by removing the word "temp" and replacing it with your current verification block name  
  (e.g. temp_env.svh => decoder_env.svh)

## 2nd Step: Replace Names Inside Files with Your Verification Block
- Open your text editor (e.g. VS Code, Sublime) and search for the word "temp", then replace all with your current verification block name  
  (e.g. temp => decoder)

## 3rd Step: Change Some Logic in the Code Itself for the Following Files:

## MODULES:

### temp_shared_pkg.sv
- You can change the TESTS localparam, which will be read by temp_sequence.svh to generate stimulus iterations based on this value (default: TESTS = 1000)
- You can change the CLK_PERIOD localparam (default: CLK_PERIOD = 10), which will be read by temp_interface.sv and used in the clock generation initial block in the interface
- You can add any parameter, localparam, classes, and typedef enum
- You can import it in temp_pkg.sv, temp_interface.sv, temp_sva.sv, and temp_top.sv

### temp_pkg.sv:
- You can add all UVM components and UVM objects using `include for .svh files (e.g. `include "temp_driver.svh")
- You can also import your temp_shared_pkg.sv here if needed

### temp_top.sv:
- You can override parameters in the Interface, DUT, or SVA instances using #() before instance name
- You can also import your temp_shared_pkg.sv here if needed
- You can change "temp_test" inside run_test(), or remove it and use +UVM_TESTNAME=temp_test inside your TCL script

### temp_sva.sv:
- You can add SVA properties (assert, cover, assume, restrict)
- You can add parameters here that can be overridden in the top module
- You can import your temp_shared_pkg.sv here if needed

### temp_interface.sv:
- You can edit `timescale 1ns/1ns to match your intended needs  
  Note: Changing the time precision here will affect the waveform GUI time scale
- You can edit the clock generation block here
- You can also import your temp_shared_pkg.sv here if needed
- You can add clocking blocks here if needed
- You can add Bus Functional Model (BFM) functions and tasks here if needed

## COMPONENTS

### temp_test.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can dump the config DB or print the UVM topology hierarchy in end_of_elaboration_phase if needed
- You can start your sequence here or in a virtual sequence class
- You can control the agent types through the configuration objects
- You can print uvm_info before and after starting the sequence with UVM_LOW verbosity

### temp_env.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can create agents and a virtual sequencer here if needed

### temp_scoreboard.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can add a golden model in the reference_model function
- You can add any TLM using export, imp, or imp_decl here if needed
- You can print uvm_info in run_phase for correct comparisons with UVM_DEBUG verbosity
- You can print uvm_error in run_phase for incorrect comparisons, including the seq_item transaction
- You can print uvm_info in report_phase for the number of transactions captured by the scoreboard to trace transactions with UVM_MEDIUM verbosity
- You can print uvm_info in report_phase for total successful and failed counts based on the comparison done in run_phase with UVM_MEDIUM verbosity

### temp_collector.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can add any TLM using export, imp, or imp_decl here if needed
- You can edit the covergroup block with the required coverpoints and cross coverage
- You can print uvm_info in report_phase for the total coverage percentage in floating radix (default: no digits after decimal point, can be edited) with UVM_MEDIUM verbosity

### temp_agent.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can check the configuration object to determine the agent type
- You can create analysis ports here if needed

### temp_driver.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can print uvm_info for seq_item transactions (input stimulus) in run_phase with UVM_HIGH verbosity
- You can add your driving logic using blocking or non-blocking assignments with clocking blocks if needed
- You can return the seq_item packet again inside item_done() for reactive agents and use get_response in sequnece if needed

### temp_sequencer.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- Advanced Note: You can create a TLM connection between the Sequencer and Monitor to monitor the input stimulus directly from the sequencer instead of the DUT, to avoid pin-level mismatches. This allows verification of the driving mechanism itself

### temp_monitor.svh:
- You can modify any phase or create user-defined phases and callback functions before and after any phase if needed
- You can print uvm_info for seq_item transactions (inputs and outputs) in run_phase with UVM_FULL verbosity
- You can print uvm_info in report_phase for the number of monitored transactions to trace activity with UVM_MEDIUM verbosity

## OBJECTS

### temp_config.svh:
- You can define the configuration for the UVM environment (e.g. agent type: passive/active, enable/disable scoreboard, etc.)

### temp_sequence.svh:
- You can modify the driving mechanism using inline constraints or [error injection class (hard constraints here, soft constraints in sequence item)]
- You can use pre_body, body, and post_body tasks if needed
- You can create base sequences such as master, slave, or reset sequences if needed
- You can use uvm_do macros if needed

### temp_sequence_item.svh:
- You can define the stimulus and transaction item to be used across components
- You can create field macros, register with the factory, and implement do_print, do_copy, do_compare, do_record functions if needed
- You can declare rand and randc variables and add constraints
- You can use pre_randomize() and post_randomize() functions if needed

## Compilation Notes:
- Compile only .sv files with this order (temp_shared_pkg.sv, temp_interface.sv, temp_pkg.sv, and temp_top.sv) using their directory path (do not compile .svh files directly, as they are included automatically)
- Compile UVM 1.2 package using its directory and +incdir
- Compile DPI libraries if needed
- Compile encrypted designs using .svp
- Define macros used in the UVM environment (e.g. +define+ASSERT_ON)
- Add coverage options (e.g. +cover -covercells)

## Simulation Notes:
- Add UVM control options (e.g. -uvmcontrol=all, +UVM_VERBOSITY=UVM_FULL, +UVM_TESTNAME=temp_test)
- Add -sv_lib (e.g. for uvm_dpi library, DPI.dll)
- Add -sv_seed (e.g. -sv_seed random)
- Add coverage options (e.g. -cover)
- Add debug and trace DB options (e.g. -classdebug, +UVM_CONFIG_DB_TRACE, etc.)
- Add optimization options (e.g. -voptargs=+acc)
