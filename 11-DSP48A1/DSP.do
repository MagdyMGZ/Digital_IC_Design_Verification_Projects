vlib work
vlog Comb_Seq_Mux.v DSP48A1.v DSP48A1_tb.v
vsim -voptargs=+acc work.DSP48A1_tb
do wave.do
run -all
# quit -sim