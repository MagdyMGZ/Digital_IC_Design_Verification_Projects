vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.ram_top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM
run 0
add wave /ram_top/DUT_RAM/*
coverage save RAM_top.ucdb -onexit -du work.RAM
run -all
coverage exclude -src ../../RTL/RAM.v -line 28 -code s
coverage exclude -src ../../RTL/RAM.v -line 28 -code b
coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report RAM_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report RAM_top.ucdb -du=RAM -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt

