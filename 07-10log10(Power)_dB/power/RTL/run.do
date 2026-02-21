vlib work
vlog multiplier.v adder.v power.v power_tb.sv +cover -covercells
vsim -voptargs=+acc work.power_tb -cover -classdebug
do wave.do
coverage save power.ucdb -onexit -du work.power
run -all
coverage exclude -du power -togglenode adder_in1
coverage exclude -du power -togglenode adder_in2
coverage exclude -du power -togglenode adder_out
coverage exclude -du power -togglenode mult_out
coverage exclude -du power -togglenode power_out
coverage exclude -du adder -togglenode adder_in1
coverage exclude -du adder -togglenode adder_in2
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report power.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report power.ucdb -du=power -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt