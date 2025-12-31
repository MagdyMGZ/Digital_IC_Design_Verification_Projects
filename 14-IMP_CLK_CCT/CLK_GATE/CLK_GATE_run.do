vlib work
vlog CLK_GATE.sv CLK_GATE_tb.sv
vsim -voptargs=+acc work.CLK_GATE_tb
add wave *
run -all
