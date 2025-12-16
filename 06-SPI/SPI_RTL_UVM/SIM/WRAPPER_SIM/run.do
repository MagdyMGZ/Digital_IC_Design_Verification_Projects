vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.wrapper_top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM
run 0
add wave /wrapper_top/DUT_WRAPPER/*
coverage save WRAPPER_top.ucdb -onexit -du work.WRAPPER
run -all
coverage exclude -src ../../RTL/RAM.v -line 28 -code b
coverage exclude -src ../../RTL/RAM.v -line 28 -code s
coverage exclude -src ../../RTL/SLAVE.sv -line 80 -code b
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report WRAPPER_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report WRAPPER_top.ucdb -du=WRAPPER -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt

