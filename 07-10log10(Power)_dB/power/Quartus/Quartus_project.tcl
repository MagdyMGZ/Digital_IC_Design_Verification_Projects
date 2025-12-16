# Create the Project
project_new power -overwrite

# Declare FPGA family, Device, Top level file 
set_global_assignment -name FAMILY "Cyclone 10 LP" 
set_global_assignment -name DEVICE 10CL010YE144I7G
set_global_assignment -name VERILOG_FILE adder.v
set_global_assignment -name VERILOG_FILE multiplier.v
set_global_assignment -name VERILOG_FILE power.v
set_global_assignment -name SDC_FILE Timing_Constraints.sdc
set_global_assignment -name TOP_LEVEL_ENTITY power