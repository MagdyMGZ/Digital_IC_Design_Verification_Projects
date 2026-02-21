vlib work
vlog *.sv +cover
vsim -voptargs=+acc work.top -classdebug -uvmcontrol=all -cover +UVM_VERBOSITY=UVM_MEDIUM 
run 0
add wave /top/alsu_IF/*
add wave /top/shift_reg_IF/*
coverage save ALSU_top.ucdb -onexit -du work.ALSU
run -all
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report ALSU_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report ALSU_top.ucdb -du=ALSU -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
