vlib work
vlog CLK_DIV.sv CLK_DIV_tb.sv
vsim -voptargs=+acc work.CLK_DIV_tb
add wave *
run -all
