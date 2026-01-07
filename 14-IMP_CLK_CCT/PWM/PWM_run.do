vlib work
vlog PWM.sv PWM_tb.sv
vsim -voptargs=+acc work.PWM_tb
add wave *
run -all
