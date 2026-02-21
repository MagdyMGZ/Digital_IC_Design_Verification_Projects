vlib work
vlog PULSE_GEN.sv PULSE_GEN_tb.sv
vsim -voptargs=+acc work.PULSE_GEN_tb
add wave /DUT/*
run -all
