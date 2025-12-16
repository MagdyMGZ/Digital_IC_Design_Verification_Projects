# Create Clock
create_clock -name clk -period 20 -waveform {0 10} [get_ports clk]

# Set false paths for Asynchronous signals
set_false_path -from [get_ports rstn]