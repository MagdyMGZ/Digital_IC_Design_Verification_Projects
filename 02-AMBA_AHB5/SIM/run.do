vlib work
vlog -f src_files.list +cover -covercells +define+SIM
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME=AHB5_test -sv_seed random
run 0
do wave.do
coverage save AHB_top.ucdb -onexit -du work.AHB5_Slave_Memory
run -all
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report AHB_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report AHB_top.ucdb -du=AHB5_Slave_Memory -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
