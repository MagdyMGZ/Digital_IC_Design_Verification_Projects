vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_HIGH +UVM_TESTNAME=FIFO_test
run 0
add wave /top/DUT/*
add wave /top/DUT/sva_inst/RST_assertion /top/DUT/sva_inst/EMPTY_assertion /top/DUT/sva_inst/ALMOSTEMPTY_assertion /top/DUT/sva_inst/ALMOSTFULL_assertion /top/DUT/sva_inst/FULL_assertion /top/DUT/sva_inst/OVERFLOW_assertion /top/DUT/sva_inst/UNDERFLOW_assertion /top/DUT/sva_inst/WR_ACK_HIGH_assertion /top/DUT/sva_inst/WR_ACK_LOW_assertion /top/DUT/sva_inst/COUNTER_INC_10_assertion /top/DUT/sva_inst/COUNTER_INC_01_assertion /top/DUT/sva_inst/COUNTER_INC_11_WR_assertion /top/DUT/sva_inst/COUNTER_INC_11_RD_assertion /top/DUT/sva_inst/COUNTER_LAT_assertion /top/DUT/sva_inst/RD_PTR_assertion /top/DUT/sva_inst/WR_PTR_assertion /top/DUT/sva_inst/WR_PTR_wraparound_assertion /top/DUT/sva_inst/RD_PTR_wraparound_assertion /top/DUT/sva_inst/COUNT_wraparound_assertion /top/DUT/sva_inst/WR_PTR_threshold_assertion /top/DUT/sva_inst/RD_PTR_threshold_assertion /top/DUT/sva_inst/COUNT_threshold_assertion
coverage save FIFO_top.ucdb -onexit -du work.FIFO
run -all
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report FIFO_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report FIFO_top.ucdb -du=FIFO -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
