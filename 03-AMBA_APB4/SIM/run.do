vlib work
vlog -f src_files.list +cover -covercells +define+SIM
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME=APB4_test -sv_seed random
run 0
add wave /top/DUT/*
coverage save APB_top.ucdb -onexit -du work.APB4_BUS_WRAPPER
run -all
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report APB_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report APB_top.ucdb -du=APB4_BUS_WRAPPER -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
