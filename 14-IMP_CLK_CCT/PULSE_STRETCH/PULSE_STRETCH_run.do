vlib work
vlog PULSE_STRETCH.sv PULSE_STRETCH_tb.sv
vsim -voptargs=+acc work.PULSE_STRETCH_tb
add wave *
run -all
