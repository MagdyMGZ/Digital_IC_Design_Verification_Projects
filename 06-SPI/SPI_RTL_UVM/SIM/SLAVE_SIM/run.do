vlib work
vlog -f src_files.list +cover -covercells +define+SIM
vsim -voptargs=+acc work.slave_top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM
run 0
add wave /slave_top/DUT_SLAVE/*
coverage save SLAVE_top.ucdb -onexit -du work.SLAVE
run -all
coverage exclude -src ../../RTL/SLAVE.sv -line 80 -code b
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report SLAVE_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report SLAVE_top.ucdb -du=SLAVE -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt

