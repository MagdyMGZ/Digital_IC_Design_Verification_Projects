# Create Clock
create_clock -name clk -period 6.667 -waveform {0 3.334} [get_ports clk];

# Set false paths for Asynchronous signals
set_false_path -from [get_ports rstn];

# Set Input Delay
set_input_delay -max 0.10 -clock [get_clocks clk] [get_ports {real_in imag_in enable_in}];    # Set input delay for setup analysis
set_input_delay -min 0.05 -clock [get_clocks clk] [get_ports {real_in imag_in enable_in}];    # Set input delay for hold analysis

# Set Output Delay
set_output_delay -max 0.10 -clock [get_clocks clk] [get_ports {power_out valid_out}];         # Set output delay for setup analysis
set_output_delay -min 0.05 -clock [get_clocks clk] [get_ports {power_out valid_out}];         # Set output delay for hold analysis