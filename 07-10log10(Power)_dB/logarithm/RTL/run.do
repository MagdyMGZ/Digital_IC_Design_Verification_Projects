vlib work
vlog log2.v log2_tb.sv dB_10log10.v dB_10log10_tb.sv
# vsim -voptargs=+acc work.log2_tb
vsim -voptargs=+acc work.dB_10log10_tb
add wave *
run -all