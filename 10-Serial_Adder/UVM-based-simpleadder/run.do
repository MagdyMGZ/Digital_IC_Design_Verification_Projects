vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_HIGH +UVM_TESTNAME=sa_test
run 0
add wave /top/DUT/*
add wave /top/DUT/sva_inst/Adder_Out_Assertion /top/DUT/sva_inst/Adder_En_O_Assertion
coverage save sa_top.ucdb -onexit
run -all
coverage exclude -du simpleadder -togglenode counter
coverage exclude -du simpleadder -togglenode state
# quit -sim
# vcover report sa_top.ucdb -details -annotate -all -output cov_report.txt
