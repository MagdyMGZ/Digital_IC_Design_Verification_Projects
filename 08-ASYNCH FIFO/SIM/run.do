vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_HIGH +UVM_TESTNAME=ASYNCH_FIFO_test
run 0
add wave /top/DUT/*
add wave /top/DUT/sva_inst/empty_cond_assertion /top/DUT/sva_inst/full_cond_assertion /top/DUT/sva_inst/rd_ptr_cond_assertion /top/DUT/sva_inst/RST_ASSERTION /top/DUT/sva_inst/wr_ptr_cond_assertion
coverage save ASYNCH_FIFO_top.ucdb -onexit -du work.ASYNCH_FIFO
run -all
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report ASYNCH_FIFO_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report ASYNCH_FIFO_top.ucdb -du=ASYNCH_FIFO -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
